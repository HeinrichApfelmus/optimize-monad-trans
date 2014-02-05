[1 of 3] Compiling ReaderImplicit   ( ReaderImplicit.hs, build/ReaderImplicit.o )

==================== Tidy Core ====================
Result size of Tidy Core = {terms: 161, types: 464, coercions: 204}

ReaderImplicit.ask1
  :: forall r_tK (m_tL :: * -> *).
     (GHC.Base.Monad m_tL, ?ask::r_tK) =>
     m_tL r_tK
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType U(AASA)L,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_tK)
                 (@ (m_tL :: * -> *))
                 ($dMonad_aib [Occ=Once] :: GHC.Base.Monad m_tL)
                 ($dIP_aie [Occ=Once] :: ?ask::r_tK) ->
                 GHC.Base.return
                   @ m_tL
                   $dMonad_aib
                   @ r_tK
                   ($dIP_aie
                    `cast` (<GHC.IP.NTCo:IP <"ask"> <r_tK>> :: ?ask::r_tK ~# r_tK))}]
ReaderImplicit.ask1 =
  \ (@ r_tK)
    (@ (m_tL :: * -> *))
    ($dMonad_aib :: GHC.Base.Monad m_tL)
    ($dIP_aie :: ?ask::r_tK) ->
    GHC.Base.return
      @ m_tL
      $dMonad_aib
      @ r_tK
      ($dIP_aie
       `cast` (<GHC.IP.NTCo:IP <"ask"> <r_tK>> :: ?ask::r_tK ~# r_tK))

ReaderImplicit.ask
  :: forall r_afb (m_afc :: * -> *).
     GHC.Base.Monad m_afc =>
     ReaderImplicit.ReaderT r_afb m_afc r_afb
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType U(AASA)L,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= ReaderImplicit.ask1
               `cast` (forall r_tK (m_tL :: * -> *).
                       <GHC.Base.Monad m_tL>
                       -> Sym <(ReaderImplicit.NTCo:ReaderT <r_tK> <m_tL> <r_tK>)>
                       :: (forall r_tK (m_tL :: * -> *).
                           (GHC.Base.Monad m_tL, ?ask::r_tK) =>
                           m_tL r_tK)
                            ~#
                          (forall r_tK (m_tL :: * -> *).
                           GHC.Base.Monad m_tL =>
                           ReaderImplicit.ReaderT r_tK m_tL r_tK))}]
ReaderImplicit.ask =
  ReaderImplicit.ask1
  `cast` (forall r_tK (m_tL :: * -> *).
          <GHC.Base.Monad m_tL>
          -> Sym <(ReaderImplicit.NTCo:ReaderT <r_tK> <m_tL> <r_tK>)>
          :: (forall r_tK (m_tL :: * -> *).
              (GHC.Base.Monad m_tL, ?ask::r_tK) =>
              m_tL r_tK)
               ~#
             (forall r_tK (m_tL :: * -> *).
              GHC.Base.Monad m_tL =>
              ReaderImplicit.ReaderT r_tK m_tL r_tK))

ReaderImplicit.readerT1
  :: forall r_t1c (m_t1d :: * -> *) a_t1e.
     GHC.Base.Monad m_t1d =>
     ((?ask::r_t1c) => m_t1d a_t1e) -> (?ask::r_t1c) => m_t1d a_t1e
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType AS,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_t1c)
                 (@ (m_t1d :: * -> *))
                 (@ a_t1e)
                 _
                 (tpl_B1 [Occ=Once] :: (?ask::r_t1c) => m_t1d a_t1e) ->
                 tpl_B1}]
ReaderImplicit.readerT1 =
  \ (@ r_t1c)
    (@ (m_t1d :: * -> *))
    (@ a_t1e)
    _
    (tpl_B1 :: (?ask::r_t1c) => m_t1d a_t1e) ->
    tpl_B1

ReaderImplicit.readerT
  :: forall r_afk (m_afl :: * -> *) a_afm.
     GHC.Base.Monad m_afl =>
     (r_afk -> m_afl a_afm) -> ReaderImplicit.ReaderT r_afk m_afl a_afm
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType AS,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= ReaderImplicit.readerT1
               `cast` (forall r_t1c (m_t1d :: * -> *) a_t1e.
                       <GHC.Base.Monad m_t1d>
                       -> (<GHC.IP.NTCo:IP <"ask"> <r_t1c>> -> <m_t1d a_t1e>)
                       -> Sym <(ReaderImplicit.NTCo:ReaderT <r_t1c> <m_t1d> <a_t1e>)>
                       :: (forall r_t1c (m_t1d :: * -> *) a_t1e.
                           GHC.Base.Monad m_t1d =>
                           ((?ask::r_t1c) => m_t1d a_t1e) -> (?ask::r_t1c) => m_t1d a_t1e)
                            ~#
                          (forall r_t1c (m_t1d :: * -> *) a_t1e.
                           GHC.Base.Monad m_t1d =>
                           (r_t1c -> m_t1d a_t1e)
                           -> ReaderImplicit.ReaderT r_t1c m_t1d a_t1e))}]
ReaderImplicit.readerT =
  ReaderImplicit.readerT1
  `cast` (forall r_t1c (m_t1d :: * -> *) a_t1e.
          <GHC.Base.Monad m_t1d>
          -> (<GHC.IP.NTCo:IP <"ask"> <r_t1c>> -> <m_t1d a_t1e>)
          -> Sym <(ReaderImplicit.NTCo:ReaderT <r_t1c> <m_t1d> <a_t1e>)>
          :: (forall r_t1c (m_t1d :: * -> *) a_t1e.
              GHC.Base.Monad m_t1d =>
              ((?ask::r_t1c) => m_t1d a_t1e) -> (?ask::r_t1c) => m_t1d a_t1e)
               ~#
             (forall r_t1c (m_t1d :: * -> *) a_t1e.
              GHC.Base.Monad m_t1d =>
              (r_t1c -> m_t1d a_t1e)
              -> ReaderImplicit.ReaderT r_t1c m_t1d a_t1e))

ReaderImplicit.runReaderT
  :: forall r_afn (m_afo :: * -> *) a_afp.
     ReaderImplicit.ReaderT r_afn m_afo a_afp -> r_afn -> m_afo a_afp
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType C(S)L,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
ReaderImplicit.runReaderT =
  \ (@ r_t1k)
    (@ (m_t1l :: * -> *))
    (@ a_t1m)
    (ds_dkd :: ReaderImplicit.ReaderT r_t1k m_t1l a_t1m)
    (r_afr :: r_t1k) ->
    (ds_dkd
     `cast` (<ReaderImplicit.NTCo:ReaderT <r_t1k> <m_t1l> <a_t1m>>
             :: ReaderImplicit.ReaderT r_t1k m_t1l a_t1m
                  ~#
                ((?ask::r_t1k) => m_t1l a_t1m)))
      (r_afr
       `cast` (Sym <(GHC.IP.NTCo:IP <"ask"> <r_t1k>)>
               :: r_t1k ~# ?ask::r_t1k))

ReaderImplicit.run
  :: forall r_af1 (m_af2 :: * -> *) a_af3.
     (?ask::r_af1) =>
     ReaderImplicit.ReaderT r_af1 m_af2 a_af3 -> m_af2 a_af3
[GblId[[RecSel]],
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType LC(S),
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
ReaderImplicit.run =
  \ (@ r_h)
    (@ (m_i :: * -> *))
    (@ a_j)
    ($dIP_ahw :: ?ask::r_h)
    (ds_dke :: ReaderImplicit.ReaderT r_h m_i a_j) ->
    (ds_dke
     `cast` (<ReaderImplicit.NTCo:ReaderT <r_h> <m_i> <a_j>>
             :: ReaderImplicit.ReaderT r_h m_i a_j ~# ((?ask::r_h) => m_i a_j)))
      $dIP_ahw

ReaderImplicit.$fMonadReaderT1
  :: forall r_afC (m_afD :: * -> *).
     GHC.Base.Monad m_afD =>
     forall a_t2e. a_t2e -> (?ask::r_afC) => m_afD a_t2e
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType U(AASA)LA,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_afC)
                 (@ (m_afD :: * -> *))
                 ($dMonad_aj9 [Occ=Once] :: GHC.Base.Monad m_afD)
                 (@ a_t2e)
                 (a1_afw [Occ=Once] :: a_t2e)
                 _ ->
                 GHC.Base.return @ m_afD $dMonad_aj9 @ a_t2e a1_afw}]
ReaderImplicit.$fMonadReaderT1 =
  \ (@ r_afC)
    (@ (m_afD :: * -> *))
    ($dMonad_aj9 :: GHC.Base.Monad m_afD)
    (@ a_t2e)
    (a1_afw :: a_t2e)
    _ ->
    GHC.Base.return @ m_afD $dMonad_aj9 @ a_t2e a1_afw

ReaderImplicit.$fMonadReaderT_$creturn
  :: forall r_afC (m_afD :: * -> *).
     GHC.Base.Monad m_afD =>
     forall a_aif. a_aif -> ReaderImplicit.ReaderT r_afC m_afD a_aif
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType U(AASA)LA,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= ReaderImplicit.$fMonadReaderT1
               `cast` (forall r_afC (m_afD :: * -> *).
                       <GHC.Base.Monad m_afD>
                       -> forall a_t2e.
                          <a_t2e>
                          -> Sym <(ReaderImplicit.NTCo:ReaderT <r_afC> <m_afD> <a_t2e>)>
                       :: (forall r_afC (m_afD :: * -> *).
                           GHC.Base.Monad m_afD =>
                           forall a_t2e. a_t2e -> (?ask::r_afC) => m_afD a_t2e)
                            ~#
                          (forall r_afC (m_afD :: * -> *).
                           GHC.Base.Monad m_afD =>
                           forall a_t2e. a_t2e -> ReaderImplicit.ReaderT r_afC m_afD a_t2e))}]
ReaderImplicit.$fMonadReaderT_$creturn =
  ReaderImplicit.$fMonadReaderT1
  `cast` (forall r_afC (m_afD :: * -> *).
          <GHC.Base.Monad m_afD>
          -> forall a_t2e.
             <a_t2e>
             -> Sym <(ReaderImplicit.NTCo:ReaderT <r_afC> <m_afD> <a_t2e>)>
          :: (forall r_afC (m_afD :: * -> *).
              GHC.Base.Monad m_afD =>
              forall a_t2e. a_t2e -> (?ask::r_afC) => m_afD a_t2e)
               ~#
             (forall r_afC (m_afD :: * -> *).
              GHC.Base.Monad m_afD =>
              forall a_t2e. a_t2e -> ReaderImplicit.ReaderT r_afC m_afD a_t2e))

ReaderImplicit.$fMonadReaderT2
  :: forall r_Xgj (m_Xgl :: * -> *).
     GHC.Base.Monad m_Xgl =>
     forall a_t26 b_t27.
     ReaderImplicit.ReaderT r_Xgj m_Xgl a_t26
     -> (a_t26 -> ReaderImplicit.ReaderT r_Xgj m_Xgl b_t27)
     -> (?ask::r_Xgj) => m_Xgl b_t27
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType U(SAAA)LLL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=4, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=False)
         Tmpl= \ (@ r_Xgj)
                 (@ (m_Xgl :: * -> *))
                 ($dMonad_XjS [Occ=Once] :: GHC.Base.Monad m_Xgl)
                 (@ a_t26)
                 (@ b_t27)
                 (m_aft [Occ=Once] :: ReaderImplicit.ReaderT r_Xgj m_Xgl a_t26)
                 (k_afu [Occ=OnceL!]
                    :: a_t26 -> ReaderImplicit.ReaderT r_Xgj m_Xgl b_t27)
                 ($dIP_aiw :: ?ask::r_Xgj) ->
                 GHC.Base.>>=
                   @ m_Xgl
                   $dMonad_XjS
                   @ a_t26
                   @ b_t27
                   ((m_aft
                     `cast` (<ReaderImplicit.NTCo:ReaderT <r_Xgj> <m_Xgl> <a_t26>>
                             :: ReaderImplicit.ReaderT r_Xgj m_Xgl a_t26
                                  ~#
                                ((?ask::r_Xgj) => m_Xgl a_t26)))
                      $dIP_aiw)
                   (\ (a1_afv [Occ=Once] :: a_t26) ->
                      ((k_afu a1_afv)
                       `cast` (<ReaderImplicit.NTCo:ReaderT <r_Xgj> <m_Xgl> <b_t27>>
                               :: ReaderImplicit.ReaderT r_Xgj m_Xgl b_t27
                                    ~#
                                  ((?ask::r_Xgj) => m_Xgl b_t27)))
                        $dIP_aiw)}]
ReaderImplicit.$fMonadReaderT2 =
  \ (@ r_Xgj)
    (@ (m_Xgl :: * -> *))
    ($dMonad_XjS :: GHC.Base.Monad m_Xgl)
    (@ a_t26)
    (@ b_t27)
    (m_aft :: ReaderImplicit.ReaderT r_Xgj m_Xgl a_t26)
    (k_afu :: a_t26 -> ReaderImplicit.ReaderT r_Xgj m_Xgl b_t27)
    ($dIP_aiw :: ?ask::r_Xgj) ->
    GHC.Base.>>=
      @ m_Xgl
      $dMonad_XjS
      @ a_t26
      @ b_t27
      ((m_aft
        `cast` (<ReaderImplicit.NTCo:ReaderT <r_Xgj> <m_Xgl> <a_t26>>
                :: ReaderImplicit.ReaderT r_Xgj m_Xgl a_t26
                     ~#
                   ((?ask::r_Xgj) => m_Xgl a_t26)))
         $dIP_aiw)
      (\ (a1_afv :: a_t26) ->
         ((k_afu a1_afv)
          `cast` (<ReaderImplicit.NTCo:ReaderT <r_Xgj> <m_Xgl> <b_t27>>
                  :: ReaderImplicit.ReaderT r_Xgj m_Xgl b_t27
                       ~#
                     ((?ask::r_Xgj) => m_Xgl b_t27)))
           $dIP_aiw)

ReaderImplicit.$fMonadReaderT_$c>>=
  :: forall r_afC (m_afD :: * -> *).
     GHC.Base.Monad m_afD =>
     forall a_aix b_aiy.
     ReaderImplicit.ReaderT r_afC m_afD a_aix
     -> (a_aix -> ReaderImplicit.ReaderT r_afC m_afD b_aiy)
     -> ReaderImplicit.ReaderT r_afC m_afD b_aiy
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType U(SAAA)LLL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= ReaderImplicit.$fMonadReaderT2
               `cast` (forall r_Xgj (m_Xgl :: * -> *).
                       <GHC.Base.Monad m_Xgl>
                       -> forall a_t26 b_t27.
                          <ReaderImplicit.ReaderT r_Xgj m_Xgl a_t26>
                          -> <a_t26 -> ReaderImplicit.ReaderT r_Xgj m_Xgl b_t27>
                          -> Sym <(ReaderImplicit.NTCo:ReaderT <r_Xgj> <m_Xgl> <b_t27>)>
                       :: (forall r_Xgj (m_Xgl :: * -> *).
                           GHC.Base.Monad m_Xgl =>
                           forall a_t26 b_t27.
                           ReaderImplicit.ReaderT r_Xgj m_Xgl a_t26
                           -> (a_t26 -> ReaderImplicit.ReaderT r_Xgj m_Xgl b_t27)
                           -> (?ask::r_Xgj) => m_Xgl b_t27)
                            ~#
                          (forall r_Xgj (m_Xgl :: * -> *).
                           GHC.Base.Monad m_Xgl =>
                           forall a_t26 b_t27.
                           ReaderImplicit.ReaderT r_Xgj m_Xgl a_t26
                           -> (a_t26 -> ReaderImplicit.ReaderT r_Xgj m_Xgl b_t27)
                           -> ReaderImplicit.ReaderT r_Xgj m_Xgl b_t27))}]
ReaderImplicit.$fMonadReaderT_$c>>= =
  ReaderImplicit.$fMonadReaderT2
  `cast` (forall r_Xgj (m_Xgl :: * -> *).
          <GHC.Base.Monad m_Xgl>
          -> forall a_t26 b_t27.
             <ReaderImplicit.ReaderT r_Xgj m_Xgl a_t26>
             -> <a_t26 -> ReaderImplicit.ReaderT r_Xgj m_Xgl b_t27>
             -> Sym <(ReaderImplicit.NTCo:ReaderT <r_Xgj> <m_Xgl> <b_t27>)>
          :: (forall r_Xgj (m_Xgl :: * -> *).
              GHC.Base.Monad m_Xgl =>
              forall a_t26 b_t27.
              ReaderImplicit.ReaderT r_Xgj m_Xgl a_t26
              -> (a_t26 -> ReaderImplicit.ReaderT r_Xgj m_Xgl b_t27)
              -> (?ask::r_Xgj) => m_Xgl b_t27)
               ~#
             (forall r_Xgj (m_Xgl :: * -> *).
              GHC.Base.Monad m_Xgl =>
              forall a_t26 b_t27.
              ReaderImplicit.ReaderT r_Xgj m_Xgl a_t26
              -> (a_t26 -> ReaderImplicit.ReaderT r_Xgj m_Xgl b_t27)
              -> ReaderImplicit.ReaderT r_Xgj m_Xgl b_t27))

ReaderImplicit.$fMonadReaderT_$cfail
  :: forall r_afC (m_afD :: * -> *).
     GHC.Base.Monad m_afD =>
     forall a_ajx.
     GHC.Base.String -> ReaderImplicit.ReaderT r_afC m_afD a_ajx
[GblId,
 Arity=2,
 Str=DmdType ASb,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_Xgs)
                 (@ (m_Xgu :: * -> *))
                 _
                 (@ a_akB)
                 (eta_B1 [Occ=Once] :: [GHC.Types.Char]) ->
                 GHC.Err.error @ (ReaderImplicit.ReaderT r_Xgs m_Xgu a_akB) eta_B1}]
ReaderImplicit.$fMonadReaderT_$cfail =
  \ (@ r_Xgs)
    (@ (m_Xgu :: * -> *))
    _
    (@ a_akB)
    (eta_B1 :: [GHC.Types.Char]) ->
    GHC.Err.error @ (ReaderImplicit.ReaderT r_Xgs m_Xgu a_akB) eta_B1

a_rld
  :: forall r_Xgr (m_Xgt :: * -> *).
     GHC.Base.Monad m_Xgt =>
     forall a_ajj b_ajk.
     ReaderImplicit.ReaderT r_Xgr m_Xgt a_ajj
     -> ReaderImplicit.ReaderT r_Xgr m_Xgt b_ajk
     -> (?ask::r_Xgr) => m_Xgt b_ajk
[GblId, Arity=4, Caf=NoCafRefs, Str=DmdType U(SAAA)LLL]
a_rld =
  \ (@ r_Xgr)
    (@ (m_Xgt :: * -> *))
    ($dMonad_Xk0 :: GHC.Base.Monad m_Xgt)
    (@ a_ajj)
    (@ b_ajk)
    (eta_B2 :: ReaderImplicit.ReaderT r_Xgr m_Xgt a_ajj)
    (eta1_B1 :: ReaderImplicit.ReaderT r_Xgr m_Xgt b_ajk)
    (eta2_X2 :: ?ask::r_Xgr) ->
    let {
      lvl1_skW :: m_Xgt b_ajk
      [LclId]
      lvl1_skW =
        (eta1_B1
         `cast` (<ReaderImplicit.NTCo:ReaderT <r_Xgr> <m_Xgt> <b_ajk>>
                 :: ReaderImplicit.ReaderT r_Xgr m_Xgt b_ajk
                      ~#
                    ((?ask::r_Xgr) => m_Xgt b_ajk)))
          eta2_X2 } in
    GHC.Base.>>=
      @ m_Xgt
      $dMonad_Xk0
      @ a_ajj
      @ b_ajk
      ((eta_B2
        `cast` (<ReaderImplicit.NTCo:ReaderT <r_Xgr> <m_Xgt> <a_ajj>>
                :: ReaderImplicit.ReaderT r_Xgr m_Xgt a_ajj
                     ~#
                   ((?ask::r_Xgr) => m_Xgt a_ajj)))
         eta2_X2)
      (\ _ -> lvl1_skW)

ReaderImplicit.$fMonadReaderT_$c>> [InlPrag=INLINE (sat-args=2)]
  :: forall r_afC (m_afD :: * -> *).
     GHC.Base.Monad m_afD =>
     forall a_ajj b_ajk.
     ReaderImplicit.ReaderT r_afC m_afD a_ajj
     -> ReaderImplicit.ReaderT r_afC m_afD b_ajk
     -> ReaderImplicit.ReaderT r_afC m_afD b_ajk
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType U(SAAA)LLL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=False,boring_ok=False)
         Tmpl= \ (@ r_Xh7)
                 (@ (m_Xha :: * -> *))
                 ($dMonad_XkI [Occ=Once] :: GHC.Base.Monad m_Xha)
                 (@ a_aku)
                 (@ b_akv)
                 (m_akw [Occ=Once] :: ReaderImplicit.ReaderT r_Xh7 m_Xha a_aku)
                 (k_akx [Occ=OnceL] :: ReaderImplicit.ReaderT r_Xh7 m_Xha b_akv) ->
                 ReaderImplicit.$fMonadReaderT_$c>>=
                   @ r_Xh7 @ m_Xha $dMonad_XkI @ a_aku @ b_akv m_akw (\ _ -> k_akx)}]
ReaderImplicit.$fMonadReaderT_$c>> =
  a_rld
  `cast` (forall r_Xgr (m_Xgt :: * -> *).
          <GHC.Base.Monad m_Xgt>
          -> forall a_ajj b_ajk.
             <ReaderImplicit.ReaderT r_Xgr m_Xgt a_ajj>
             -> <ReaderImplicit.ReaderT r_Xgr m_Xgt b_ajk>
             -> Sym <(ReaderImplicit.NTCo:ReaderT <r_Xgr> <m_Xgt> <b_ajk>)>
          :: (forall r_Xgr (m_Xgt :: * -> *).
              GHC.Base.Monad m_Xgt =>
              forall a_ajj b_ajk.
              ReaderImplicit.ReaderT r_Xgr m_Xgt a_ajj
              -> ReaderImplicit.ReaderT r_Xgr m_Xgt b_ajk
              -> (?ask::r_Xgr) => m_Xgt b_ajk)
               ~#
             (forall r_Xgr (m_Xgt :: * -> *).
              GHC.Base.Monad m_Xgt =>
              forall a_ajj b_ajk.
              ReaderImplicit.ReaderT r_Xgr m_Xgt a_ajj
              -> ReaderImplicit.ReaderT r_Xgr m_Xgt b_ajk
              -> ReaderImplicit.ReaderT r_Xgr m_Xgt b_ajk))

lvl_rle
  :: forall r_Xgq (m_Xgs :: * -> *) a_akB.
     [GHC.Types.Char] -> ReaderImplicit.ReaderT r_Xgq m_Xgs a_akB
[GblId, Arity=1, Str=DmdType Tb]
lvl_rle =
  \ (@ r_Xgq)
    (@ (m_Xgs :: * -> *))
    (@ a_akB)
    (eta_B1 :: [GHC.Types.Char]) ->
    GHC.Err.error @ (ReaderImplicit.ReaderT r_Xgq m_Xgs a_akB) eta_B1

ReaderImplicit.$fMonadReaderT [InlPrag=[ALWAYS] CONLIKE]
  :: forall r_afC (m_afD :: * -> *).
     GHC.Base.Monad m_afD =>
     GHC.Base.Monad (ReaderImplicit.ReaderT r_afC m_afD)
[GblId[DFunId],
 Arity=1,
 Str=DmdType Lm,
 Unf=DFun(arity=3) GHC.Base.D:Monad [{ReaderImplicit.$fMonadReaderT_$c>>=},
                                     {ReaderImplicit.$fMonadReaderT_$c>>},
                                     {ReaderImplicit.$fMonadReaderT_$creturn},
                                     {ReaderImplicit.$fMonadReaderT_$cfail}]]
ReaderImplicit.$fMonadReaderT =
  \ (@ r_Xgq)
    (@ (m_Xgs :: * -> *))
    ($dMonad_XjZ :: GHC.Base.Monad m_Xgs) ->
    let {
      lvl1_skY :: forall a_t2e. a_t2e -> m_Xgs a_t2e
      [LclId]
      lvl1_skY =
        \ (@ a_t2e) -> GHC.Base.return @ m_Xgs $dMonad_XjZ @ a_t2e } in
    GHC.Base.D:Monad
      @ (ReaderImplicit.ReaderT r_Xgq m_Xgs)
      ((ReaderImplicit.$fMonadReaderT2 @ r_Xgq @ m_Xgs $dMonad_XjZ)
       `cast` (forall a_t26 b_t27.
               <ReaderImplicit.ReaderT r_Xgq m_Xgs a_t26>
               -> <a_t26 -> ReaderImplicit.ReaderT r_Xgq m_Xgs b_t27>
               -> Sym <(ReaderImplicit.NTCo:ReaderT <r_Xgq> <m_Xgs> <b_t27>)>
               :: (forall a_t26 b_t27.
                   ReaderImplicit.ReaderT r_Xgq m_Xgs a_t26
                   -> (a_t26 -> ReaderImplicit.ReaderT r_Xgq m_Xgs b_t27)
                   -> (?ask::r_Xgq) => m_Xgs b_t27)
                    ~#
                  (forall a_t26 b_t27.
                   ReaderImplicit.ReaderT r_Xgq m_Xgs a_t26
                   -> (a_t26 -> ReaderImplicit.ReaderT r_Xgq m_Xgs b_t27)
                   -> ReaderImplicit.ReaderT r_Xgq m_Xgs b_t27)))
      (ReaderImplicit.$fMonadReaderT_$c>> @ r_Xgq @ m_Xgs $dMonad_XjZ)
      ((\ (@ a_t2e) (a1_afw :: a_t2e) _ -> lvl1_skY @ a_t2e a1_afw)
       `cast` (forall a_t2e.
               <a_t2e>
               -> Sym <(ReaderImplicit.NTCo:ReaderT <r_Xgq> <m_Xgs> <a_t2e>)>
               :: (forall a_t2e. a_t2e -> (?ask::r_Xgq) => m_Xgs a_t2e)
                    ~#
                  (forall a_t2e. a_t2e -> ReaderImplicit.ReaderT r_Xgq m_Xgs a_t2e)))
      (lvl_rle @ r_Xgq @ m_Xgs)

ReaderImplicit.$fMonadIOReaderT1
  :: forall r_afA (m_afB :: * -> *).
     (GHC.Base.Monad (ReaderImplicit.ReaderT r_afA m_afB),
      Control.Monad.IO.Class.MonadIO m_afB) =>
     forall a_t22. GHC.Types.IO a_t22 -> (?ask::r_afA) => m_afB a_t22
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType AU(AS)LA,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=4, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_afA)
                 (@ (m_afB :: * -> *))
                 _
                 ($dMonadIO_aiZ [Occ=Once] :: Control.Monad.IO.Class.MonadIO m_afB)
                 (@ a_t22)
                 (m_afx [Occ=Once] :: GHC.Types.IO a_t22)
                 _ ->
                 Control.Monad.IO.Class.liftIO @ m_afB $dMonadIO_aiZ @ a_t22 m_afx}]
ReaderImplicit.$fMonadIOReaderT1 =
  \ (@ r_afA)
    (@ (m_afB :: * -> *))
    _
    ($dMonadIO_aiZ :: Control.Monad.IO.Class.MonadIO m_afB)
    (@ a_t22)
    (m_afx :: GHC.Types.IO a_t22)
    _ ->
    Control.Monad.IO.Class.liftIO @ m_afB $dMonadIO_aiZ @ a_t22 m_afx

ReaderImplicit.$fMonadIOReaderT_$cliftIO
  :: forall r_afA (m_afB :: * -> *).
     (GHC.Base.Monad (ReaderImplicit.ReaderT r_afA m_afB),
      Control.Monad.IO.Class.MonadIO m_afB) =>
     forall a_ai6.
     GHC.Types.IO a_ai6 -> ReaderImplicit.ReaderT r_afA m_afB a_ai6
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType AU(AS)LA,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= ReaderImplicit.$fMonadIOReaderT1
               `cast` (forall r_afA (m_afB :: * -> *).
                       <GHC.Base.Monad (ReaderImplicit.ReaderT r_afA m_afB)>
                       -> <Control.Monad.IO.Class.MonadIO m_afB>
                       -> forall a_t22.
                          <GHC.Types.IO a_t22>
                          -> Sym <(ReaderImplicit.NTCo:ReaderT <r_afA> <m_afB> <a_t22>)>
                       :: (forall r_afA (m_afB :: * -> *).
                           (GHC.Base.Monad (ReaderImplicit.ReaderT r_afA m_afB),
                            Control.Monad.IO.Class.MonadIO m_afB) =>
                           forall a_t22. GHC.Types.IO a_t22 -> (?ask::r_afA) => m_afB a_t22)
                            ~#
                          (forall r_afA (m_afB :: * -> *).
                           (GHC.Base.Monad (ReaderImplicit.ReaderT r_afA m_afB),
                            Control.Monad.IO.Class.MonadIO m_afB) =>
                           forall a_t22.
                           GHC.Types.IO a_t22 -> ReaderImplicit.ReaderT r_afA m_afB a_t22))}]
ReaderImplicit.$fMonadIOReaderT_$cliftIO =
  ReaderImplicit.$fMonadIOReaderT1
  `cast` (forall r_afA (m_afB :: * -> *).
          <GHC.Base.Monad (ReaderImplicit.ReaderT r_afA m_afB)>
          -> <Control.Monad.IO.Class.MonadIO m_afB>
          -> forall a_t22.
             <GHC.Types.IO a_t22>
             -> Sym <(ReaderImplicit.NTCo:ReaderT <r_afA> <m_afB> <a_t22>)>
          :: (forall r_afA (m_afB :: * -> *).
              (GHC.Base.Monad (ReaderImplicit.ReaderT r_afA m_afB),
               Control.Monad.IO.Class.MonadIO m_afB) =>
              forall a_t22. GHC.Types.IO a_t22 -> (?ask::r_afA) => m_afB a_t22)
               ~#
             (forall r_afA (m_afB :: * -> *).
              (GHC.Base.Monad (ReaderImplicit.ReaderT r_afA m_afB),
               Control.Monad.IO.Class.MonadIO m_afB) =>
              forall a_t22.
              GHC.Types.IO a_t22 -> ReaderImplicit.ReaderT r_afA m_afB a_t22))

ReaderImplicit.$fMonadIOReaderT [InlPrag=[ALWAYS] CONLIKE]
  :: forall r_afA (m_afB :: * -> *).
     (GHC.Base.Monad (ReaderImplicit.ReaderT r_afA m_afB),
      Control.Monad.IO.Class.MonadIO m_afB) =>
     Control.Monad.IO.Class.MonadIO (ReaderImplicit.ReaderT r_afA m_afB)
[GblId[DFunId[1]],
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType LLm,
 Unf=DFun(arity=4) Control.Monad.IO.Class.D:MonadIO [<2>,
                                                     {ReaderImplicit.$fMonadIOReaderT_$cliftIO}]]
ReaderImplicit.$fMonadIOReaderT =
  \ (@ r_Xgy)
    (@ (m_XgA :: * -> *))
    ($dMonad_XjY
       :: GHC.Base.Monad (ReaderImplicit.ReaderT r_Xgy m_XgA))
    ($dMonadIO_XkN :: Control.Monad.IO.Class.MonadIO m_XgA) ->
    let {
      lvl1_skZ :: forall a_t22. GHC.Types.IO a_t22 -> m_XgA a_t22
      [LclId]
      lvl1_skZ =
        \ (@ a_t22) ->
          Control.Monad.IO.Class.liftIO @ m_XgA $dMonadIO_XkN @ a_t22 } in
    Control.Monad.IO.Class.D:MonadIO
      @ (ReaderImplicit.ReaderT r_Xgy m_XgA)
      $dMonad_XjY
      ((\ (@ a_t22) (m_afx :: GHC.Types.IO a_t22) _ ->
          lvl1_skZ @ a_t22 m_afx)
       `cast` (forall a_t22.
               <GHC.Types.IO a_t22>
               -> Sym <(ReaderImplicit.NTCo:ReaderT <r_Xgy> <m_XgA> <a_t22>)>
               :: (forall a_t22.
                   GHC.Types.IO a_t22 -> (?ask::r_Xgy) => m_XgA a_t22)
                    ~#
                  (forall a_t22.
                   GHC.Types.IO a_t22 -> ReaderImplicit.ReaderT r_Xgy m_XgA a_t22)))

ReaderImplicit.$fMonadTransReaderT1
  :: forall r_afz (m_t1X :: * -> *) a_t1Y.
     GHC.Base.Monad m_t1X =>
     m_t1X a_t1Y -> (?ask::r_afz) => m_t1X a_t1Y
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType ASA,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_afz)
                 (@ (m_t1X :: * -> *))
                 (@ a_t1Y)
                 _
                 (eta_XR [Occ=Once] :: m_t1X a_t1Y)
                 _ ->
                 eta_XR}]
ReaderImplicit.$fMonadTransReaderT1 =
  \ (@ r_afz)
    (@ (m_t1X :: * -> *))
    (@ a_t1Y)
    _
    (eta_XR :: m_t1X a_t1Y)
    _ ->
    eta_XR

ReaderImplicit.$fMonadTransReaderT_$clift
  :: forall r_afz (m_aiT :: * -> *) a_aiU.
     GHC.Base.Monad m_aiT =>
     m_aiT a_aiU -> ReaderImplicit.ReaderT r_afz m_aiT a_aiU
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType ASA,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= ReaderImplicit.$fMonadTransReaderT1
               `cast` (forall r_afz (m_t1X :: * -> *) a_t1Y.
                       <GHC.Base.Monad m_t1X>
                       -> <m_t1X a_t1Y>
                       -> Sym <(ReaderImplicit.NTCo:ReaderT <r_afz> <m_t1X> <a_t1Y>)>
                       :: (forall r_afz (m_t1X :: * -> *) a_t1Y.
                           GHC.Base.Monad m_t1X =>
                           m_t1X a_t1Y -> (?ask::r_afz) => m_t1X a_t1Y)
                            ~#
                          (forall r_afz (m_t1X :: * -> *) a_t1Y.
                           GHC.Base.Monad m_t1X =>
                           m_t1X a_t1Y -> ReaderImplicit.ReaderT r_afz m_t1X a_t1Y))}]
ReaderImplicit.$fMonadTransReaderT_$clift =
  ReaderImplicit.$fMonadTransReaderT1
  `cast` (forall r_afz (m_t1X :: * -> *) a_t1Y.
          <GHC.Base.Monad m_t1X>
          -> <m_t1X a_t1Y>
          -> Sym <(ReaderImplicit.NTCo:ReaderT <r_afz> <m_t1X> <a_t1Y>)>
          :: (forall r_afz (m_t1X :: * -> *) a_t1Y.
              GHC.Base.Monad m_t1X =>
              m_t1X a_t1Y -> (?ask::r_afz) => m_t1X a_t1Y)
               ~#
             (forall r_afz (m_t1X :: * -> *) a_t1Y.
              GHC.Base.Monad m_t1X =>
              m_t1X a_t1Y -> ReaderImplicit.ReaderT r_afz m_t1X a_t1Y))

ReaderImplicit.$fMonadTransReaderT [InlPrag=INLINE (sat-args=0)]
  :: forall r_afz.
     Control.Monad.Trans.Class.MonadTrans (ReaderImplicit.ReaderT r_afz)
[GblId[DFunId(nt)],
 Str=DmdType,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=False,boring_ok=True)
         Tmpl= ReaderImplicit.$fMonadTransReaderT_$clift
               `cast` (forall r_Xhj.
                       Sym
                         <(Control.Monad.Trans.Class.NTCo:MonadTrans
                             <ReaderImplicit.ReaderT r_Xhj>)>
                       :: (forall r_Xhj (m_aiT :: * -> *) a_aiU.
                           GHC.Base.Monad m_aiT =>
                           m_aiT a_aiU -> ReaderImplicit.ReaderT r_Xhj m_aiT a_aiU)
                            ~#
                          (forall r_Xhj.
                           Control.Monad.Trans.Class.MonadTrans
                             (ReaderImplicit.ReaderT r_Xhj)))}]
ReaderImplicit.$fMonadTransReaderT =
  ReaderImplicit.$fMonadTransReaderT1
  `cast` (forall r_afz.
          (forall (m_t1X :: * -> *) a_t1Y.
           <GHC.Base.Monad m_t1X>
           -> <m_t1X a_t1Y>
           -> Sym
                <(ReaderImplicit.NTCo:ReaderT <r_afz> <m_t1X> <a_t1Y>)>) ; Sym
                                                                             <(Control.Monad.Trans.Class.NTCo:MonadTrans
                                                                                 <ReaderImplicit.ReaderT
                                                                                    r_afz>)>
          :: (forall r_afz (m_t1X :: * -> *) a_t1Y.
              GHC.Base.Monad m_t1X =>
              m_t1X a_t1Y -> (?ask::r_afz) => m_t1X a_t1Y)
               ~#
             (forall r_afz.
              Control.Monad.Trans.Class.MonadTrans
                (ReaderImplicit.ReaderT r_afz)))



[2 of 3] Compiling Eval1            ( Eval1.hs, build/Eval1.o )

==================== Tidy Core ====================
Result size of Tidy Core = {terms: 46, types: 101, coercions: 95}

Eval1.runEval2 :: GHC.Types.Int
[GblId,
 Caf=NoCafRefs,
 Str=DmdType m,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=False, Expandable=True,
         Guidance=IF_ARGS [] 10 20}]
Eval1.runEval2 = GHC.Types.I# 0

Eval1.runEval1
  :: forall void_l.
     Eval1.Eval void_l
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #)
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType LL,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=IF_ARGS [0 0] 47 0}]
Eval1.runEval1 =
  \ (@ void_l)
    (m_atm :: Eval1.Eval void_l)
    (eta_B1 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    case GHC.Prim.newMutVar#
           @ GHC.Types.Int @ GHC.Prim.RealWorld Eval1.runEval2 eta_B1
    of _ { (# ipv_av3, ipv1_av4 #) ->
    let {
      a_svr :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
      [LclId, Str=DmdType m]
      a_svr =
        GHC.STRef.STRef @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_av4 } in
    case (((((m_atm
              `cast` (<ReaderImplicit.NTCo:ReaderT
                         <Eval1.Value>
                         <ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO>
                         <void_l>>
                      :: ReaderImplicit.ReaderT
                           Eval1.Value
                           (ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO)
                           void_l
                           ~#
                         ((?ask::Eval1.Value) =>
                          ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO void_l)))
               (a_svr
                `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int> ; Sym
                                                                         <(GHC.IP.NTCo:IP
                                                                             <"ask"> <Eval1.Value>)>
                        :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                             ~#
                           ?ask::Eval1.Value)))
            `cast` (<ReaderImplicit.NTCo:ReaderT
                       <Eval1.Value> <GHC.Types.IO> <void_l>>
                    :: ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO void_l
                         ~#
                       ((?ask::Eval1.Value) => GHC.Types.IO void_l)))
             (a_svr
              `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int> ; Sym
                                                                       <(GHC.IP.NTCo:IP
                                                                           <"ask"> <Eval1.Value>)>
                      :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                           ~#
                         ?ask::Eval1.Value)))
          `cast` (<GHC.Types.NTCo:IO <void_l>>
                  :: GHC.Types.IO void_l
                       ~#
                     (GHC.Prim.State# GHC.Prim.RealWorld
                      -> (# GHC.Prim.State# GHC.Prim.RealWorld, void_l #))))
           ipv_av3
    of _ { (# ipv2_XvO, _ #) ->
    GHC.Prim.readMutVar#
      @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_av4 ipv2_XvO
    }
    }

Eval1.runEval
  :: forall void_atl.
     Eval1.Eval void_atl -> GHC.Types.IO GHC.Types.Int
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType LL,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval1.runEval =
  Eval1.runEval1
  `cast` (forall void_l.
          <Eval1.Eval void_l> -> Sym <(GHC.Types.NTCo:IO <GHC.Types.Int>)>
          :: (forall void_l.
              Eval1.Eval void_l
              -> GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #))
               ~#
             (forall void_l. Eval1.Eval void_l -> GHC.Types.IO GHC.Types.Int))

Eval1.ask3
  :: (?ask::Eval1.Value, ?ask::GHC.IORef.IORef GHC.Types.Int) =>
     GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval1.Value #)
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType LAL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ ($dIP_aie [Occ=Once] :: ?ask::Eval1.Value)
                 _
                 (s_avI [Occ=Once] :: GHC.Prim.State# GHC.Prim.RealWorld) ->
                 (# s_avI,
                    $dIP_aie
                    `cast` (<GHC.IP.NTCo:IP <"ask"> <Eval1.Value>>
                            :: ?ask::Eval1.Value ~# Eval1.Value) #)}]
Eval1.ask3 =
  \ ($dIP_aie :: ?ask::Eval1.Value)
    _
    (s_avI :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# s_avI,
       $dIP_aie
       `cast` (<GHC.IP.NTCo:IP <"ask"> <Eval1.Value>>
               :: ?ask::Eval1.Value ~# Eval1.Value) #)

Eval1.ask1 :: Eval1.Eval Eval1.Value
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType LAL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Eval1.ask3
               `cast` ((<?ask::Eval1.Value>
                        -> (<?ask::GHC.IORef.IORef GHC.Types.Int>
                            -> Sym <(GHC.Types.NTCo:IO <Eval1.Value>)>) ; Sym
                                                                            <(ReaderImplicit.NTCo:ReaderT
                                                                                <GHC.IORef.IORef
                                                                                   GHC.Types.Int>
                                                                                <GHC.Types.IO>
                                                                                <Eval1.Value>)>) ; Sym
                                                                                                     <(ReaderImplicit.NTCo:ReaderT
                                                                                                         <Eval1.Value>
                                                                                                         <ReaderImplicit.ReaderT
                                                                                                            Eval1.Value
                                                                                                            GHC.Types.IO>
                                                                                                         <Eval1.Value>)>
                       :: ((?ask::Eval1.Value, ?ask::GHC.IORef.IORef GHC.Types.Int) =>
                           GHC.Prim.State# GHC.Prim.RealWorld
                           -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval1.Value #))
                            ~#
                          ReaderImplicit.ReaderT
                            Eval1.Value
                            (ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO)
                            Eval1.Value)}]
Eval1.ask1 =
  Eval1.ask3
  `cast` ((<?ask::Eval1.Value>
           -> (<?ask::GHC.IORef.IORef GHC.Types.Int>
               -> Sym <(GHC.Types.NTCo:IO <Eval1.Value>)>) ; Sym
                                                               <(ReaderImplicit.NTCo:ReaderT
                                                                   <GHC.IORef.IORef GHC.Types.Int>
                                                                   <GHC.Types.IO>
                                                                   <Eval1.Value>)>) ; Sym
                                                                                        <(ReaderImplicit.NTCo:ReaderT
                                                                                            <Eval1.Value>
                                                                                            <ReaderImplicit.ReaderT
                                                                                               Eval1.Value
                                                                                               GHC.Types.IO>
                                                                                            <Eval1.Value>)>
          :: ((?ask::Eval1.Value, ?ask::GHC.IORef.IORef GHC.Types.Int) =>
              GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval1.Value #))
               ~#
             ReaderImplicit.ReaderT
               Eval1.Value
               (ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO)
               Eval1.Value)

Eval1.ask4
  :: (?ask::GHC.IORef.IORef GHC.Types.Int, ?ask::Eval1.Value) =>
     GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval1.Value #)
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType ALL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ _
                 (eta_B2 [Occ=Once] :: ?ask::Eval1.Value)
                 (eta2_B1 [Occ=Once] :: GHC.Prim.State# GHC.Prim.RealWorld) ->
                 (# eta2_B1,
                    eta_B2
                    `cast` (<GHC.IP.NTCo:IP <"ask"> <Eval1.Value>>
                            :: ?ask::Eval1.Value ~# Eval1.Value) #)}]
Eval1.ask4 =
  \ _
    (eta_B2 :: ?ask::Eval1.Value)
    (eta2_B1 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# eta2_B1,
       eta_B2
       `cast` (<GHC.IP.NTCo:IP <"ask"> <Eval1.Value>>
               :: ?ask::Eval1.Value ~# Eval1.Value) #)

Eval1.ask2 :: Eval1.Eval Eval1.Value
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType ALL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Eval1.ask4
               `cast` ((<?ask::GHC.IORef.IORef GHC.Types.Int>
                        -> (<?ask::Eval1.Value>
                            -> Sym <(GHC.Types.NTCo:IO <Eval1.Value>)>) ; Sym
                                                                            <(ReaderImplicit.NTCo:ReaderT
                                                                                <Eval1.Value>
                                                                                <GHC.Types.IO>
                                                                                <Eval1.Value>)>) ; Sym
                                                                                                     <(ReaderImplicit.NTCo:ReaderT
                                                                                                         <GHC.IORef.IORef
                                                                                                            GHC.Types.Int>
                                                                                                         <ReaderImplicit.ReaderT
                                                                                                            Eval1.Value
                                                                                                            GHC.Types.IO>
                                                                                                         <Eval1.Value>)>
                       :: ((?ask::GHC.IORef.IORef GHC.Types.Int, ?ask::Eval1.Value) =>
                           GHC.Prim.State# GHC.Prim.RealWorld
                           -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval1.Value #))
                            ~#
                          ReaderImplicit.ReaderT
                            (GHC.IORef.IORef GHC.Types.Int)
                            (ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO)
                            Eval1.Value)}]
Eval1.ask2 =
  Eval1.ask4
  `cast` ((<?ask::GHC.IORef.IORef GHC.Types.Int>
           -> (<?ask::Eval1.Value>
               -> Sym <(GHC.Types.NTCo:IO <Eval1.Value>)>) ; Sym
                                                               <(ReaderImplicit.NTCo:ReaderT
                                                                   <Eval1.Value>
                                                                   <GHC.Types.IO>
                                                                   <Eval1.Value>)>) ; Sym
                                                                                        <(ReaderImplicit.NTCo:ReaderT
                                                                                            <GHC.IORef.IORef
                                                                                               GHC.Types.Int>
                                                                                            <ReaderImplicit.ReaderT
                                                                                               Eval1.Value
                                                                                               GHC.Types.IO>
                                                                                            <Eval1.Value>)>
          :: ((?ask::GHC.IORef.IORef GHC.Types.Int, ?ask::Eval1.Value) =>
              GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval1.Value #))
               ~#
             ReaderImplicit.ReaderT
               (GHC.IORef.IORef GHC.Types.Int)
               (ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO)
               Eval1.Value)



[3 of 3] Compiling OptimizeMonadTrans ( OptimizeMonadTrans.hs, build/OptimizeMonadTrans.o )

==================== Tidy Core ====================
Result size of Tidy Core = {terms: 179, types: 278, coercions: 202}

a_r11u :: GHC.Types.Int
[GblId, Caf=NoCafRefs, Str=DmdType m]
a_r11u = GHC.Types.I# 1

a1_r11v
  :: (?ask::GHC.IORef.IORef GHC.Types.Int,
      ?ask::GHC.IORef.IORef GHC.Types.Int) =>
     GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #)
[GblId, Arity=3, Caf=NoCafRefs, Str=DmdType AAL]
a1_r11v =
  \ _ _ (s_avI :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# s_avI, a_r11u #)

a2_r11w :: GHC.Types.Int
[GblId, Caf=NoCafRefs, Str=DmdType m]
a2_r11w = GHC.Types.I# 2

a3_r11x
  :: (?ask::GHC.IORef.IORef GHC.Types.Int,
      ?ask::GHC.IORef.IORef GHC.Types.Int) =>
     GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #)
[GblId, Arity=3, Caf=NoCafRefs, Str=DmdType AAL]
a3_r11x =
  \ _ _ (s_avI :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# s_avI, a2_r11w #)

a4_r11y :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a4_r11y =
  GHC.Types.:
    @ OptimizeMonadTrans.Tree
    OptimizeMonadTrans.Leaf
    (GHC.Types.[] @ OptimizeMonadTrans.Tree)

a5_r11z :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a5_r11z =
  GHC.Types.:
    @ OptimizeMonadTrans.Tree OptimizeMonadTrans.Leaf a4_r11y

a6_r11A :: OptimizeMonadTrans.Tree
[GblId, Caf=NoCafRefs, Str=DmdType]
a6_r11A =
  OptimizeMonadTrans.Branch
    (a3_r11x
     `cast` ((<?ask::GHC.IORef.IORef GHC.Types.Int>
              -> (<?ask::GHC.IORef.IORef GHC.Types.Int>
                  -> Sym <(GHC.Types.NTCo:IO <GHC.Types.Int>)>) ; Sym
                                                                    <(ReaderImplicit.NTCo:ReaderT
                                                                        <GHC.IORef.IORef
                                                                           GHC.Types.Int>
                                                                        <GHC.Types.IO>
                                                                        <GHC.Types.Int>)>) ; Sym
                                                                                               <(ReaderImplicit.NTCo:ReaderT
                                                                                                   <GHC.IORef.IORef
                                                                                                      GHC.Types.Int>
                                                                                                   <ReaderImplicit.ReaderT
                                                                                                      Eval1.Value
                                                                                                      GHC.Types.IO>
                                                                                                   <GHC.Types.Int>)>
             :: ((?ask::GHC.IORef.IORef GHC.Types.Int,
                  ?ask::GHC.IORef.IORef GHC.Types.Int) =>
                 GHC.Prim.State# GHC.Prim.RealWorld
                 -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #))
                  ~#
                ReaderImplicit.ReaderT
                  (GHC.IORef.IORef GHC.Types.Int)
                  (ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO)
                  GHC.Types.Int))
    a5_r11z

a7_r11B :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a7_r11B = GHC.Types.: @ OptimizeMonadTrans.Tree a6_r11A a4_r11y

tree_ryq :: OptimizeMonadTrans.Tree
[GblId, Caf=NoCafRefs, Str=DmdType]
tree_ryq =
  OptimizeMonadTrans.Branch
    (a1_r11v
     `cast` ((<?ask::GHC.IORef.IORef GHC.Types.Int>
              -> (<?ask::GHC.IORef.IORef GHC.Types.Int>
                  -> Sym <(GHC.Types.NTCo:IO <GHC.Types.Int>)>) ; Sym
                                                                    <(ReaderImplicit.NTCo:ReaderT
                                                                        <GHC.IORef.IORef
                                                                           GHC.Types.Int>
                                                                        <GHC.Types.IO>
                                                                        <GHC.Types.Int>)>) ; Sym
                                                                                               <(ReaderImplicit.NTCo:ReaderT
                                                                                                   <GHC.IORef.IORef
                                                                                                      GHC.Types.Int>
                                                                                                   <ReaderImplicit.ReaderT
                                                                                                      Eval1.Value
                                                                                                      GHC.Types.IO>
                                                                                                   <GHC.Types.Int>)>
             :: ((?ask::GHC.IORef.IORef GHC.Types.Int,
                  ?ask::GHC.IORef.IORef GHC.Types.Int) =>
                 GHC.Prim.State# GHC.Prim.RealWorld
                 -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #))
                  ~#
                ReaderImplicit.ReaderT
                  (GHC.IORef.IORef GHC.Types.Int)
                  (ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO)
                  GHC.Types.Int))
    a7_r11B

lvl_r11C
  :: (?ask::GHC.IORef.IORef GHC.Types.Int) =>
     GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld,
           [OptimizeMonadTrans.Tree] #)
[GblId, Arity=2, Caf=NoCafRefs]
lvl_r11C =
  \ (eta_B2 :: ?ask::GHC.IORef.IORef GHC.Types.Int)
    (eta1_Xw :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    case eta_B2
         `cast` (<GHC.IP.NTCo:IP
                    <"ask"> <Eval1.Value>> ; <GHC.IORef.NTCo:IORef> <GHC.Types.Int>
                 :: ?ask::Eval1.Value
                      ~#
                    GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int)
    of _ { GHC.STRef.STRef var#_avy ->
    case GHC.Prim.readMutVar#
           @ GHC.Prim.RealWorld @ GHC.Types.Int var#_avy eta1_Xw
    of _ { (# ipv_avm, ipv1_avn #) ->
    case ipv1_avn of _ { GHC.Types.I# x_aJh ->
    case GHC.Prim.writeMutVar#
           @ GHC.Prim.RealWorld
           @ GHC.Types.Int
           var#_avy
           (GHC.Types.I# (GHC.Prim.+# x_aJh 1))
           ipv_avm
    of s2#_aKQ { __DEFAULT ->
    (# s2#_aKQ, GHC.Types.[] @ OptimizeMonadTrans.Tree #)
    }
    }
    }
    }

lvl1_r11D
  :: (?ask::GHC.IORef.IORef GHC.Types.Int) =>
     GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #)
[GblId, Arity=2, Caf=NoCafRefs]
lvl1_r11D =
  \ _ (s_Xwj :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# s_Xwj, GHC.Tuple.() #)

Rec {
a8_r11E
  :: [OptimizeMonadTrans.Tree]
     -> (?ask::Eval1.Value) =>
        ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO ()
[GblId, Arity=2, Caf=NoCafRefs, Str=DmdType SL]
a8_r11E =
  \ (ds_dHG :: [OptimizeMonadTrans.Tree])
    (eta_B1 :: ?ask::Eval1.Value) ->
    case ds_dHG of _ {
      [] ->
        lvl1_r11D
        `cast` ((<?ask::GHC.IORef.IORef GHC.Types.Int>
                 -> Sym <(GHC.Types.NTCo:IO <()>)>) ; Sym
                                                        <(ReaderImplicit.NTCo:ReaderT
                                                            <GHC.IORef.IORef GHC.Types.Int>
                                                            <GHC.Types.IO>
                                                            <()>)>
                :: ((?ask::GHC.IORef.IORef GHC.Types.Int) =>
                    GHC.Prim.State# GHC.Prim.RealWorld
                    -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #))
                     ~#
                   ReaderImplicit.ReaderT
                     (GHC.IORef.IORef GHC.Types.Int) GHC.Types.IO ());
      : x_aBW xs_aBX ->
        let {
          m_XgS [Dmd=Just L]
            :: ReaderImplicit.ReaderT
                 (GHC.IORef.IORef GHC.Types.Int)
                 GHC.Types.IO
                 [OptimizeMonadTrans.Tree]
          [LclId, Str=DmdType]
          m_XgS =
            case x_aBW of _ {
              OptimizeMonadTrans.Branch action_aBZ children_aC0 ->
                let {
                  m1_XgU [Dmd=Just L]
                    :: ReaderImplicit.ReaderT
                         (GHC.IORef.IORef GHC.Types.Int) GHC.Types.IO GHC.Types.Int
                  [LclId, Str=DmdType]
                  m1_XgU =
                    (action_aBZ
                     `cast` (<ReaderImplicit.NTCo:ReaderT
                                <GHC.IORef.IORef GHC.Types.Int>
                                <ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO>
                                <GHC.Types.Int>>
                             :: ReaderImplicit.ReaderT
                                  (GHC.IORef.IORef GHC.Types.Int)
                                  (ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO)
                                  GHC.Types.Int
                                  ~#
                                ((?ask::GHC.IORef.IORef GHC.Types.Int) =>
                                 ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO GHC.Types.Int)))
                      eta_B1 } in
                (\ ($dIP_Xk0 :: ?ask::GHC.IORef.IORef GHC.Types.Int)
                   (s_avj :: GHC.Prim.State# GHC.Prim.RealWorld) ->
                   case (((m1_XgU
                           `cast` (<ReaderImplicit.NTCo:ReaderT
                                      <GHC.IORef.IORef GHC.Types.Int>
                                      <GHC.Types.IO>
                                      <GHC.Types.Int>>
                                   :: ReaderImplicit.ReaderT
                                        (GHC.IORef.IORef GHC.Types.Int) GHC.Types.IO GHC.Types.Int
                                        ~#
                                      ((?ask::GHC.IORef.IORef GHC.Types.Int) =>
                                       GHC.Types.IO GHC.Types.Int)))
                            $dIP_Xk0)
                         `cast` (<GHC.Types.NTCo:IO <GHC.Types.Int>>
                                 :: GHC.Types.IO GHC.Types.Int
                                      ~#
                                    (GHC.Prim.State# GHC.Prim.RealWorld
                                     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #))))
                          s_avj
                   of _ { (# ipv_avm, ipv1_avn #) ->
                   case eta_B1
                        `cast` (<GHC.IP.NTCo:IP
                                   <"ask"> <Eval1.Value>> ; <GHC.IORef.NTCo:IORef> <GHC.Types.Int>
                                :: ?ask::Eval1.Value
                                     ~#
                                   GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int)
                   of _ { GHC.STRef.STRef var#_avy ->
                   case GHC.Prim.readMutVar#
                          @ GHC.Prim.RealWorld @ GHC.Types.Int var#_avy ipv_avm
                   of _ { (# ipv2_Xw9, ipv3_Xwb #) ->
                   case ipv1_avn of _ { GHC.Types.I# x1_aJh ->
                   case ipv3_Xwb of _ { GHC.Types.I# y_aJl ->
                   case GHC.Prim.writeMutVar#
                          @ GHC.Prim.RealWorld
                          @ GHC.Types.Int
                          var#_avy
                          (GHC.Types.I# (GHC.Prim.+# x1_aJh y_aJl))
                          ipv2_Xw9
                   of s2#_aKQ { __DEFAULT ->
                   (# s2#_aKQ, children_aC0 #)
                   }
                   }
                   }
                   }
                   }
                   })
                `cast` ((<?ask::GHC.IORef.IORef GHC.Types.Int>
                         -> Sym <(GHC.Types.NTCo:IO <[OptimizeMonadTrans.Tree]>)>) ; Sym
                                                                                       <(ReaderImplicit.NTCo:ReaderT
                                                                                           <GHC.IORef.IORef
                                                                                              GHC.Types.Int>
                                                                                           <GHC.Types.IO>
                                                                                           <[OptimizeMonadTrans.Tree]>)>
                        :: ((?ask::GHC.IORef.IORef GHC.Types.Int) =>
                            GHC.Prim.State# GHC.Prim.RealWorld
                            -> (# GHC.Prim.State# GHC.Prim.RealWorld,
                                  [OptimizeMonadTrans.Tree] #))
                             ~#
                           ReaderImplicit.ReaderT
                             (GHC.IORef.IORef GHC.Types.Int)
                             GHC.Types.IO
                             [OptimizeMonadTrans.Tree]);
              OptimizeMonadTrans.Leaf ->
                lvl_r11C
                `cast` ((<?ask::GHC.IORef.IORef GHC.Types.Int>
                         -> Sym <(GHC.Types.NTCo:IO <[OptimizeMonadTrans.Tree]>)>) ; Sym
                                                                                       <(ReaderImplicit.NTCo:ReaderT
                                                                                           <GHC.IORef.IORef
                                                                                              GHC.Types.Int>
                                                                                           <GHC.Types.IO>
                                                                                           <[OptimizeMonadTrans.Tree]>)>
                        :: ((?ask::GHC.IORef.IORef GHC.Types.Int) =>
                            GHC.Prim.State# GHC.Prim.RealWorld
                            -> (# GHC.Prim.State# GHC.Prim.RealWorld,
                                  [OptimizeMonadTrans.Tree] #))
                             ~#
                           ReaderImplicit.ReaderT
                             (GHC.IORef.IORef GHC.Types.Int)
                             GHC.Types.IO
                             [OptimizeMonadTrans.Tree])
            } } in
        (\ ($dIP_XjZ :: ?ask::GHC.IORef.IORef GHC.Types.Int)
           (s_avj :: GHC.Prim.State# GHC.Prim.RealWorld) ->
           case (((m_XgS
                   `cast` (<ReaderImplicit.NTCo:ReaderT
                              <GHC.IORef.IORef GHC.Types.Int>
                              <GHC.Types.IO>
                              <[OptimizeMonadTrans.Tree]>>
                           :: ReaderImplicit.ReaderT
                                (GHC.IORef.IORef GHC.Types.Int)
                                GHC.Types.IO
                                [OptimizeMonadTrans.Tree]
                                ~#
                              ((?ask::GHC.IORef.IORef GHC.Types.Int) =>
                               GHC.Types.IO [OptimizeMonadTrans.Tree])))
                    $dIP_XjZ)
                 `cast` (<GHC.Types.NTCo:IO <[OptimizeMonadTrans.Tree]>>
                         :: GHC.Types.IO [OptimizeMonadTrans.Tree]
                              ~#
                            (GHC.Prim.State# GHC.Prim.RealWorld
                             -> (# GHC.Prim.State# GHC.Prim.RealWorld,
                                   [OptimizeMonadTrans.Tree] #))))
                  s_avj
           of _ { (# ipv_avm, ipv1_avn #) ->
           ((((a8_r11E
                 (GHC.Base.++ @ OptimizeMonadTrans.Tree ipv1_avn xs_aBX) eta_B1)
              `cast` (<ReaderImplicit.NTCo:ReaderT
                         <GHC.IORef.IORef GHC.Types.Int> <GHC.Types.IO> <()>>
                      :: ReaderImplicit.ReaderT
                           (GHC.IORef.IORef GHC.Types.Int) GHC.Types.IO ()
                           ~#
                         ((?ask::GHC.IORef.IORef GHC.Types.Int) => GHC.Types.IO ())))
               $dIP_XjZ)
            `cast` (<GHC.Types.NTCo:IO <()>>
                    :: GHC.Types.IO ()
                         ~#
                       (GHC.Prim.State# GHC.Prim.RealWorld
                        -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #))))
             ipv_avm
           })
        `cast` ((<?ask::GHC.IORef.IORef GHC.Types.Int>
                 -> Sym <(GHC.Types.NTCo:IO <()>)>) ; Sym
                                                        <(ReaderImplicit.NTCo:ReaderT
                                                            <GHC.IORef.IORef GHC.Types.Int>
                                                            <GHC.Types.IO>
                                                            <()>)>
                :: ((?ask::GHC.IORef.IORef GHC.Types.Int) =>
                    GHC.Prim.State# GHC.Prim.RealWorld
                    -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #))
                     ~#
                   ReaderImplicit.ReaderT
                     (GHC.IORef.IORef GHC.Types.Int) GHC.Types.IO ())
    }
end Rec }

a9_r11F :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a9_r11F =
  GHC.Types.:
    @ OptimizeMonadTrans.Tree
    tree_ryq
    (GHC.Types.[] @ OptimizeMonadTrans.Tree)

a10_r11G
  :: (?ask::Eval1.Value) =>
     ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO ()
[GblId, Arity=1, Str=DmdType]
a10_r11G = a8_r11E a9_r11F

OptimizeMonadTrans.example [InlPrag=NOINLINE] :: Eval1.Eval ()
[GblId, Str=DmdType]
OptimizeMonadTrans.example =
  a10_r11G
  `cast` (Sym
            <(ReaderImplicit.NTCo:ReaderT
                <Eval1.Value>
                <ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO>
                <()>)>
          :: ((?ask::Eval1.Value) =>
              ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO ())
               ~#
             ReaderImplicit.ReaderT
               Eval1.Value (ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO) ())

OptimizeMonadTrans.main1
  :: GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #)
[GblId,
 Arity=1,
 Str=DmdType L,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=1, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=IF_ARGS [0] 117 0}]
OptimizeMonadTrans.main1 =
  \ (s_avj :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    case GHC.Prim.newMutVar#
           @ GHC.Types.Int @ GHC.Prim.RealWorld Eval1.runEval2 s_avj
    of _ { (# ipv_av3, ipv1_av4 #) ->
    let {
      a11_svr :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
      [LclId, Str=DmdType m]
      a11_svr =
        GHC.STRef.STRef @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_av4 } in
    case (((((OptimizeMonadTrans.example
              `cast` (<ReaderImplicit.NTCo:ReaderT
                         <Eval1.Value>
                         <ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO>
                         <()>>
                      :: ReaderImplicit.ReaderT
                           Eval1.Value (ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO) ()
                           ~#
                         ((?ask::Eval1.Value) =>
                          ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO ())))
               (a11_svr
                `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int> ; Sym
                                                                         <(GHC.IP.NTCo:IP
                                                                             <"ask"> <Eval1.Value>)>
                        :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                             ~#
                           ?ask::Eval1.Value)))
            `cast` (<ReaderImplicit.NTCo:ReaderT
                       <Eval1.Value> <GHC.Types.IO> <()>>
                    :: ReaderImplicit.ReaderT Eval1.Value GHC.Types.IO ()
                         ~#
                       ((?ask::Eval1.Value) => GHC.Types.IO ())))
             (a11_svr
              `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int> ; Sym
                                                                       <(GHC.IP.NTCo:IP
                                                                           <"ask"> <Eval1.Value>)>
                      :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                           ~#
                         ?ask::Eval1.Value)))
          `cast` (<GHC.Types.NTCo:IO <()>>
                  :: GHC.Types.IO ()
                       ~#
                     (GHC.Prim.State# GHC.Prim.RealWorld
                      -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #))))
           ipv_av3
    of _ { (# ipv2_XvO, _ #) ->
    case GHC.Prim.readMutVar#
           @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_av4 ipv2_XvO
    of _ { (# ipv4_avm, ipv5_avn #) ->
    GHC.IO.Handle.Text.hPutStr2
      GHC.IO.Handle.FD.stdout
      (GHC.Show.$fShowInt_$cshow ipv5_avn)
      GHC.Types.True
      ipv4_avm
    }
    }
    }

OptimizeMonadTrans.main :: GHC.Types.IO ()
[GblId,
 Arity=1,
 Str=DmdType L,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
OptimizeMonadTrans.main =
  OptimizeMonadTrans.main1
  `cast` (Sym <(GHC.Types.NTCo:IO <()>)>
          :: (GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #))
               ~#
             GHC.Types.IO ())



