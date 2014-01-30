[1 of 3] Compiling Reader           ( Reader.hs, build/Reader.o )

==================== Tidy Core ====================
Result size of Tidy Core = {terms: 131, types: 346, coercions: 144}

Reader.ask1
  :: forall r_tA (m_tB :: * -> *).
     GHC.Base.Monad m_tB =>
     r_tA -> m_tB r_tA
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType U(AASA)L,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_tA)
                 (@ (m_tB :: * -> *))
                 ($dMonad_ag9 [Occ=Once] :: GHC.Base.Monad m_tB)
                 (r_afy [Occ=Once] :: r_tA) ->
                 GHC.Base.return @ m_tB $dMonad_ag9 @ r_tA r_afy}]
Reader.ask1 =
  \ (@ r_tA)
    (@ (m_tB :: * -> *))
    ($dMonad_ag9 :: GHC.Base.Monad m_tB)
    (r_afy :: r_tA) ->
    GHC.Base.return @ m_tB $dMonad_ag9 @ r_tA r_afy

Reader.ask
  :: forall r_afj (m_afk :: * -> *).
     GHC.Base.Monad m_afk =>
     Reader.ReaderT r_afj m_afk r_afj
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType U(AASA)L,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Reader.ask1
               `cast` (forall r_tA (m_tB :: * -> *).
                       <GHC.Base.Monad m_tB>
                       -> Sym <(Reader.NTCo:ReaderT <r_tA> <m_tB> <r_tA>)>
                       :: (forall r_tA (m_tB :: * -> *).
                           GHC.Base.Monad m_tB =>
                           r_tA -> m_tB r_tA)
                            ~#
                          (forall r_tA (m_tB :: * -> *).
                           GHC.Base.Monad m_tB =>
                           Reader.ReaderT r_tA m_tB r_tA))}]
Reader.ask =
  Reader.ask1
  `cast` (forall r_tA (m_tB :: * -> *).
          <GHC.Base.Monad m_tB>
          -> Sym <(Reader.NTCo:ReaderT <r_tA> <m_tB> <r_tA>)>
          :: (forall r_tA (m_tB :: * -> *).
              GHC.Base.Monad m_tB =>
              r_tA -> m_tB r_tA)
               ~#
             (forall r_tA (m_tB :: * -> *).
              GHC.Base.Monad m_tB =>
              Reader.ReaderT r_tA m_tB r_tA))

Reader.runReaderT1
  :: forall r_h (m_i :: * -> *) a_j.
     Reader.ReaderT r_h m_i a_j -> Reader.ReaderT r_h m_i a_j
[GblId,
 Arity=1,
 Caf=NoCafRefs,
 Str=DmdType S,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=1, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Reader.runReaderT1 =
  \ (@ r_h)
    (@ (m_i :: * -> *))
    (@ a_j)
    (ds_dhw :: Reader.ReaderT r_h m_i a_j) ->
    ds_dhw

Reader.runReaderT
  :: forall r_afc (m_afd :: * -> *) a_afe.
     Reader.ReaderT r_afc m_afd a_afe -> r_afc -> m_afd a_afe
[GblId[[RecSel]],
 Arity=1,
 Caf=NoCafRefs,
 Str=DmdType S,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Reader.runReaderT =
  Reader.runReaderT1
  `cast` (forall r_h (m_i :: * -> *) a_j.
          <Reader.ReaderT r_h m_i a_j>
          -> <Reader.NTCo:ReaderT <r_h> <m_i> <a_j>>
          :: (forall r_h (m_i :: * -> *) a_j.
              Reader.ReaderT r_h m_i a_j -> Reader.ReaderT r_h m_i a_j)
               ~#
             (forall r_h (m_i :: * -> *) a_j.
              Reader.ReaderT r_h m_i a_j -> r_h -> m_i a_j))

Reader.$fMonadReaderT_$creturn
  :: forall r_afG (m_afH :: * -> *).
     GHC.Base.Monad m_afH =>
     forall a_agb. a_agb -> Reader.ReaderT r_afG m_afH a_agb
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType LL,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=IF_ARGS [30 0] 50 60}]
Reader.$fMonadReaderT_$creturn =
  \ (@ r_afG)
    (@ (m_afH :: * -> *))
    ($dMonad_agJ :: GHC.Base.Monad m_afH)
    (@ a_t1E)
    (a1_afw :: a_t1E) ->
    let {
      lvl1_si1 [Dmd=Just L] :: m_afH a_t1E
      [LclId, Str=DmdType]
      lvl1_si1 = GHC.Base.return @ m_afH $dMonad_agJ @ a_t1E a1_afw } in
    (\ _ -> lvl1_si1)
    `cast` (Sym <(Reader.NTCo:ReaderT <r_afG> <m_afH> <a_t1E>)>
            :: (r_afG -> m_afH a_t1E) ~# Reader.ReaderT r_afG m_afH a_t1E)

Reader.$fMonadReaderT1
  :: forall r_afG (m_afH :: * -> *).
     GHC.Base.Monad m_afH =>
     forall a_t1w b_t1x.
     Reader.ReaderT r_afG m_afH a_t1w
     -> (a_t1w -> Reader.ReaderT r_afG m_afH b_t1x)
     -> r_afG
     -> m_afH b_t1x
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType U(SAAA)LLL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=4, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=False)
         Tmpl= \ (@ r_afG)
                 (@ (m_afH :: * -> *))
                 ($dMonad_agJ [Occ=Once] :: GHC.Base.Monad m_afH)
                 (@ a_t1w)
                 (@ b_t1x)
                 (m_afs [Occ=Once] :: Reader.ReaderT r_afG m_afH a_t1w)
                 (k_aft [Occ=OnceL!] :: a_t1w -> Reader.ReaderT r_afG m_afH b_t1x)
                 (r_afu :: r_afG) ->
                 GHC.Base.>>=
                   @ m_afH
                   $dMonad_agJ
                   @ a_t1w
                   @ b_t1x
                   ((m_afs
                     `cast` (<Reader.NTCo:ReaderT <r_afG> <m_afH> <a_t1w>>
                             :: Reader.ReaderT r_afG m_afH a_t1w ~# (r_afG -> m_afH a_t1w)))
                      r_afu)
                   (\ (a1_afv [Occ=Once] :: a_t1w) ->
                      ((k_aft a1_afv)
                       `cast` (<Reader.NTCo:ReaderT <r_afG> <m_afH> <b_t1x>>
                               :: Reader.ReaderT r_afG m_afH b_t1x ~# (r_afG -> m_afH b_t1x)))
                        r_afu)}]
Reader.$fMonadReaderT1 =
  \ (@ r_afG)
    (@ (m_afH :: * -> *))
    ($dMonad_agJ :: GHC.Base.Monad m_afH)
    (@ a_t1w)
    (@ b_t1x)
    (m_afs :: Reader.ReaderT r_afG m_afH a_t1w)
    (k_aft :: a_t1w -> Reader.ReaderT r_afG m_afH b_t1x)
    (r_afu :: r_afG) ->
    GHC.Base.>>=
      @ m_afH
      $dMonad_agJ
      @ a_t1w
      @ b_t1x
      ((m_afs
        `cast` (<Reader.NTCo:ReaderT <r_afG> <m_afH> <a_t1w>>
                :: Reader.ReaderT r_afG m_afH a_t1w ~# (r_afG -> m_afH a_t1w)))
         r_afu)
      (\ (a1_afv :: a_t1w) ->
         ((k_aft a1_afv)
          `cast` (<Reader.NTCo:ReaderT <r_afG> <m_afH> <b_t1x>>
                  :: Reader.ReaderT r_afG m_afH b_t1x ~# (r_afG -> m_afH b_t1x)))
           r_afu)

Reader.$fMonadReaderT_$c>>=
  :: forall r_afG (m_afH :: * -> *).
     GHC.Base.Monad m_afH =>
     forall a_agm b_agn.
     Reader.ReaderT r_afG m_afH a_agm
     -> (a_agm -> Reader.ReaderT r_afG m_afH b_agn)
     -> Reader.ReaderT r_afG m_afH b_agn
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType U(SAAA)LLL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Reader.$fMonadReaderT1
               `cast` (forall r_afG (m_afH :: * -> *).
                       <GHC.Base.Monad m_afH>
                       -> forall a_t1w b_t1x.
                          <Reader.ReaderT r_afG m_afH a_t1w>
                          -> <a_t1w -> Reader.ReaderT r_afG m_afH b_t1x>
                          -> Sym <(Reader.NTCo:ReaderT <r_afG> <m_afH> <b_t1x>)>
                       :: (forall r_afG (m_afH :: * -> *).
                           GHC.Base.Monad m_afH =>
                           forall a_t1w b_t1x.
                           Reader.ReaderT r_afG m_afH a_t1w
                           -> (a_t1w -> Reader.ReaderT r_afG m_afH b_t1x)
                           -> r_afG
                           -> m_afH b_t1x)
                            ~#
                          (forall r_afG (m_afH :: * -> *).
                           GHC.Base.Monad m_afH =>
                           forall a_t1w b_t1x.
                           Reader.ReaderT r_afG m_afH a_t1w
                           -> (a_t1w -> Reader.ReaderT r_afG m_afH b_t1x)
                           -> Reader.ReaderT r_afG m_afH b_t1x))}]
Reader.$fMonadReaderT_$c>>= =
  Reader.$fMonadReaderT1
  `cast` (forall r_afG (m_afH :: * -> *).
          <GHC.Base.Monad m_afH>
          -> forall a_t1w b_t1x.
             <Reader.ReaderT r_afG m_afH a_t1w>
             -> <a_t1w -> Reader.ReaderT r_afG m_afH b_t1x>
             -> Sym <(Reader.NTCo:ReaderT <r_afG> <m_afH> <b_t1x>)>
          :: (forall r_afG (m_afH :: * -> *).
              GHC.Base.Monad m_afH =>
              forall a_t1w b_t1x.
              Reader.ReaderT r_afG m_afH a_t1w
              -> (a_t1w -> Reader.ReaderT r_afG m_afH b_t1x)
              -> r_afG
              -> m_afH b_t1x)
               ~#
             (forall r_afG (m_afH :: * -> *).
              GHC.Base.Monad m_afH =>
              forall a_t1w b_t1x.
              Reader.ReaderT r_afG m_afH a_t1w
              -> (a_t1w -> Reader.ReaderT r_afG m_afH b_t1x)
              -> Reader.ReaderT r_afG m_afH b_t1x))

Reader.$fMonadReaderT_$cfail
  :: forall r_afG (m_afH :: * -> *).
     GHC.Base.Monad m_afH =>
     forall a_ah7. GHC.Base.String -> Reader.ReaderT r_afG m_afH a_ah7
[GblId,
 Arity=2,
 Str=DmdType ASb,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_Xgi)
                 (@ (m_Xgk :: * -> *))
                 _
                 (@ a_ahP)
                 (eta_B1 [Occ=Once] :: [GHC.Types.Char]) ->
                 GHC.Err.error @ (Reader.ReaderT r_Xgi m_Xgk a_ahP) eta_B1}]
Reader.$fMonadReaderT_$cfail =
  \ (@ r_Xgi)
    (@ (m_Xgk :: * -> *))
    _
    (@ a_ahP)
    (eta_B1 :: [GHC.Types.Char]) ->
    GHC.Err.error @ (Reader.ReaderT r_Xgi m_Xgk a_ahP) eta_B1

a_riv
  :: forall r_Xgj (m_Xgl :: * -> *).
     GHC.Base.Monad m_Xgl =>
     forall a_agT b_agU.
     Reader.ReaderT r_Xgj m_Xgl a_agT
     -> Reader.ReaderT r_Xgj m_Xgl b_agU -> r_Xgj -> m_Xgl b_agU
[GblId, Arity=4, Caf=NoCafRefs, Str=DmdType U(SAAA)LLL]
a_riv =
  \ (@ r_Xgj)
    (@ (m_Xgl :: * -> *))
    ($dMonad_Xho :: GHC.Base.Monad m_Xgl)
    (@ a_agT)
    (@ b_agU)
    (eta_B2 :: Reader.ReaderT r_Xgj m_Xgl a_agT)
    (eta1_B1 :: Reader.ReaderT r_Xgj m_Xgl b_agU)
    (eta2_X2 :: r_Xgj) ->
    let {
      lvl1_sip :: m_Xgl b_agU
      [LclId]
      lvl1_sip =
        (eta1_B1
         `cast` (<Reader.NTCo:ReaderT <r_Xgj> <m_Xgl> <b_agU>>
                 :: Reader.ReaderT r_Xgj m_Xgl b_agU ~# (r_Xgj -> m_Xgl b_agU)))
          eta2_X2 } in
    GHC.Base.>>=
      @ m_Xgl
      $dMonad_Xho
      @ a_agT
      @ b_agU
      ((eta_B2
        `cast` (<Reader.NTCo:ReaderT <r_Xgj> <m_Xgl> <a_agT>>
                :: Reader.ReaderT r_Xgj m_Xgl a_agT ~# (r_Xgj -> m_Xgl a_agT)))
         eta2_X2)
      (\ _ -> lvl1_sip)

Reader.$fMonadReaderT_$c>> [InlPrag=INLINE (sat-args=2)]
  :: forall r_afG (m_afH :: * -> *).
     GHC.Base.Monad m_afH =>
     forall a_agT b_agU.
     Reader.ReaderT r_afG m_afH a_agT
     -> Reader.ReaderT r_afG m_afH b_agU
     -> Reader.ReaderT r_afG m_afH b_agU
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType U(SAAA)LLL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=False,boring_ok=False)
         Tmpl= \ (@ r_XgP)
                 (@ (m_XgS :: * -> *))
                 ($dMonad_XhW [Occ=Once] :: GHC.Base.Monad m_XgS)
                 (@ a_ahI)
                 (@ b_ahJ)
                 (m_ahK [Occ=Once] :: Reader.ReaderT r_XgP m_XgS a_ahI)
                 (k_ahL [Occ=OnceL] :: Reader.ReaderT r_XgP m_XgS b_ahJ) ->
                 Reader.$fMonadReaderT_$c>>=
                   @ r_XgP @ m_XgS $dMonad_XhW @ a_ahI @ b_ahJ m_ahK (\ _ -> k_ahL)}]
Reader.$fMonadReaderT_$c>> =
  a_riv
  `cast` (forall r_Xgj (m_Xgl :: * -> *).
          <GHC.Base.Monad m_Xgl>
          -> forall a_agT b_agU.
             <Reader.ReaderT r_Xgj m_Xgl a_agT>
             -> <Reader.ReaderT r_Xgj m_Xgl b_agU>
             -> Sym <(Reader.NTCo:ReaderT <r_Xgj> <m_Xgl> <b_agU>)>
          :: (forall r_Xgj (m_Xgl :: * -> *).
              GHC.Base.Monad m_Xgl =>
              forall a_agT b_agU.
              Reader.ReaderT r_Xgj m_Xgl a_agT
              -> Reader.ReaderT r_Xgj m_Xgl b_agU -> r_Xgj -> m_Xgl b_agU)
               ~#
             (forall r_Xgj (m_Xgl :: * -> *).
              GHC.Base.Monad m_Xgl =>
              forall a_agT b_agU.
              Reader.ReaderT r_Xgj m_Xgl a_agT
              -> Reader.ReaderT r_Xgj m_Xgl b_agU
              -> Reader.ReaderT r_Xgj m_Xgl b_agU))

lvl_riw
  :: forall r_Xgk (m_Xgm :: * -> *) a_ahP.
     [GHC.Types.Char] -> Reader.ReaderT r_Xgk m_Xgm a_ahP
[GblId, Arity=1, Str=DmdType Tb]
lvl_riw =
  \ (@ r_Xgk)
    (@ (m_Xgm :: * -> *))
    (@ a_ahP)
    (eta_XC :: [GHC.Types.Char]) ->
    GHC.Err.error @ (Reader.ReaderT r_Xgk m_Xgm a_ahP) eta_XC

Reader.$fMonadReaderT [InlPrag=[ALWAYS] CONLIKE]
  :: forall r_afG (m_afH :: * -> *).
     GHC.Base.Monad m_afH =>
     GHC.Base.Monad (Reader.ReaderT r_afG m_afH)
[GblId[DFunId],
 Arity=1,
 Str=DmdType Lm,
 Unf=DFun(arity=3) GHC.Base.D:Monad [{Reader.$fMonadReaderT_$c>>=},
                                     {Reader.$fMonadReaderT_$c>>}, {Reader.$fMonadReaderT_$creturn},
                                     {Reader.$fMonadReaderT_$cfail}]]
Reader.$fMonadReaderT =
  \ (@ r_Xgk)
    (@ (m_Xgm :: * -> *))
    ($dMonad_Xhp :: GHC.Base.Monad m_Xgm) ->
    GHC.Base.D:Monad
      @ (Reader.ReaderT r_Xgk m_Xgm)
      ((Reader.$fMonadReaderT1 @ r_Xgk @ m_Xgm $dMonad_Xhp)
       `cast` (forall a_X2f b_X2h.
               <Reader.ReaderT r_Xgk m_Xgm a_X2f>
               -> <a_X2f -> Reader.ReaderT r_Xgk m_Xgm b_X2h>
               -> Sym <(Reader.NTCo:ReaderT <r_Xgk> <m_Xgm> <b_X2h>)>
               :: (forall a_X2f b_X2h.
                   Reader.ReaderT r_Xgk m_Xgm a_X2f
                   -> (a_X2f -> Reader.ReaderT r_Xgk m_Xgm b_X2h)
                   -> r_Xgk
                   -> m_Xgm b_X2h)
                    ~#
                  (forall a_X2f b_X2h.
                   Reader.ReaderT r_Xgk m_Xgm a_X2f
                   -> (a_X2f -> Reader.ReaderT r_Xgk m_Xgm b_X2h)
                   -> Reader.ReaderT r_Xgk m_Xgm b_X2h)))
      (Reader.$fMonadReaderT_$c>> @ r_Xgk @ m_Xgm $dMonad_Xhp)
      (Reader.$fMonadReaderT_$creturn @ r_Xgk @ m_Xgm $dMonad_Xhp)
      (lvl_riw @ r_Xgk @ m_Xgm)

Reader.$fMonadIOReaderT_$cliftIO
  :: forall r_afE (m_afF :: * -> *).
     (GHC.Base.Monad (Reader.ReaderT r_afE m_afF),
      Control.Monad.IO.Class.MonadIO m_afF) =>
     forall a_ag3.
     GHC.Types.IO a_ag3 -> Reader.ReaderT r_afE m_afF a_ag3
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType ALL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=False)
         Tmpl= \ (@ r_afE)
                 (@ (m_afF :: * -> *))
                 _
                 ($dMonadIO_agz [Occ=Once] :: Control.Monad.IO.Class.MonadIO m_afF)
                 (@ a_t1s)
                 (m_afz [Occ=Once] :: GHC.Types.IO a_t1s) ->
                 let {
                   lvl1_si4 [Occ=OnceL, Dmd=Just L] :: m_afF a_t1s
                   [LclId, Str=DmdType]
                   lvl1_si4 =
                     Control.Monad.IO.Class.liftIO
                       @ m_afF $dMonadIO_agz @ a_t1s m_afz } in
                 (\ _ -> lvl1_si4)
                 `cast` (Sym <(Reader.NTCo:ReaderT <r_afE> <m_afF> <a_t1s>)>
                         :: (r_afE -> m_afF a_t1s) ~# Reader.ReaderT r_afE m_afF a_t1s)}]
Reader.$fMonadIOReaderT_$cliftIO =
  \ (@ r_afE)
    (@ (m_afF :: * -> *))
    _
    ($dMonadIO_agz :: Control.Monad.IO.Class.MonadIO m_afF)
    (@ a_t1s)
    (m_afz :: GHC.Types.IO a_t1s) ->
    let {
      lvl1_si4 [Dmd=Just L] :: m_afF a_t1s
      [LclId, Str=DmdType]
      lvl1_si4 =
        Control.Monad.IO.Class.liftIO
          @ m_afF $dMonadIO_agz @ a_t1s m_afz } in
    (\ _ -> lvl1_si4)
    `cast` (Sym <(Reader.NTCo:ReaderT <r_afE> <m_afF> <a_t1s>)>
            :: (r_afE -> m_afF a_t1s) ~# Reader.ReaderT r_afE m_afF a_t1s)

Reader.$fMonadIOReaderT [InlPrag=[ALWAYS] CONLIKE]
  :: forall r_afE (m_afF :: * -> *).
     (GHC.Base.Monad (Reader.ReaderT r_afE m_afF),
      Control.Monad.IO.Class.MonadIO m_afF) =>
     Control.Monad.IO.Class.MonadIO (Reader.ReaderT r_afE m_afF)
[GblId[DFunId[1]],
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType LLm,
 Unf=DFun(arity=4) Control.Monad.IO.Class.D:MonadIO [<2>,
                                                     {Reader.$fMonadIOReaderT_$cliftIO}]]
Reader.$fMonadIOReaderT =
  \ (@ r_afE)
    (@ (m_afF :: * -> *))
    ($dMonad_agy :: GHC.Base.Monad (Reader.ReaderT r_afE m_afF))
    ($dMonadIO_agz :: Control.Monad.IO.Class.MonadIO m_afF) ->
    Control.Monad.IO.Class.D:MonadIO
      @ (Reader.ReaderT r_afE m_afF)
      $dMonad_agy
      (Reader.$fMonadIOReaderT_$cliftIO
         @ r_afE @ m_afF $dMonad_agy $dMonadIO_agz)

Reader.$fMonadTransReaderT1
  :: forall r_afB (m_t1n :: * -> *) a_t1o.
     GHC.Base.Monad m_t1n =>
     m_t1n a_t1o -> r_afB -> m_t1n a_t1o
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType ASA,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_afB)
                 (@ (m_t1n :: * -> *))
                 (@ a_t1o)
                 _
                 (m_afC [Occ=Once] :: m_t1n a_t1o)
                 _ ->
                 m_afC}]
Reader.$fMonadTransReaderT1 =
  \ (@ r_afB)
    (@ (m_t1n :: * -> *))
    (@ a_t1o)
    _
    (m_afC :: m_t1n a_t1o)
    _ ->
    m_afC

Reader.$fMonadTransReaderT_$clift
  :: forall r_afB (m_agt :: * -> *) a_agu.
     GHC.Base.Monad m_agt =>
     m_agt a_agu -> Reader.ReaderT r_afB m_agt a_agu
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType ASA,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Reader.$fMonadTransReaderT1
               `cast` (forall r_afB (m_t1n :: * -> *) a_t1o.
                       <GHC.Base.Monad m_t1n>
                       -> <m_t1n a_t1o>
                       -> Sym <(Reader.NTCo:ReaderT <r_afB> <m_t1n> <a_t1o>)>
                       :: (forall r_afB (m_t1n :: * -> *) a_t1o.
                           GHC.Base.Monad m_t1n =>
                           m_t1n a_t1o -> r_afB -> m_t1n a_t1o)
                            ~#
                          (forall r_afB (m_t1n :: * -> *) a_t1o.
                           GHC.Base.Monad m_t1n =>
                           m_t1n a_t1o -> Reader.ReaderT r_afB m_t1n a_t1o))}]
Reader.$fMonadTransReaderT_$clift =
  Reader.$fMonadTransReaderT1
  `cast` (forall r_afB (m_t1n :: * -> *) a_t1o.
          <GHC.Base.Monad m_t1n>
          -> <m_t1n a_t1o>
          -> Sym <(Reader.NTCo:ReaderT <r_afB> <m_t1n> <a_t1o>)>
          :: (forall r_afB (m_t1n :: * -> *) a_t1o.
              GHC.Base.Monad m_t1n =>
              m_t1n a_t1o -> r_afB -> m_t1n a_t1o)
               ~#
             (forall r_afB (m_t1n :: * -> *) a_t1o.
              GHC.Base.Monad m_t1n =>
              m_t1n a_t1o -> Reader.ReaderT r_afB m_t1n a_t1o))

Reader.$fMonadTransReaderT [InlPrag=INLINE (sat-args=0)]
  :: forall r_afB.
     Control.Monad.Trans.Class.MonadTrans (Reader.ReaderT r_afB)
[GblId[DFunId(nt)],
 Str=DmdType,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=False,boring_ok=True)
         Tmpl= Reader.$fMonadTransReaderT_$clift
               `cast` (forall r_Xgr.
                       Sym
                         <(Control.Monad.Trans.Class.NTCo:MonadTrans
                             <Reader.ReaderT r_Xgr>)>
                       :: (forall r_Xgr (m_agt :: * -> *) a_agu.
                           GHC.Base.Monad m_agt =>
                           m_agt a_agu -> Reader.ReaderT r_Xgr m_agt a_agu)
                            ~#
                          (forall r_Xgr.
                           Control.Monad.Trans.Class.MonadTrans (Reader.ReaderT r_Xgr)))}]
Reader.$fMonadTransReaderT =
  Reader.$fMonadTransReaderT1
  `cast` (forall r_Xgr.
          (forall (m_X2e :: * -> *) a_X2g.
           <GHC.Base.Monad m_X2e>
           -> <m_X2e a_X2g>
           -> Sym <(Reader.NTCo:ReaderT <r_Xgr> <m_X2e> <a_X2g>)>) ; Sym
                                                                       <(Control.Monad.Trans.Class.NTCo:MonadTrans
                                                                           <Reader.ReaderT r_Xgr>)>
          :: (forall r_Xgr (m_X2e :: * -> *) a_X2g.
              GHC.Base.Monad m_X2e =>
              m_X2e a_X2g -> r_Xgr -> m_X2e a_X2g)
               ~#
             (forall r_Xgr.
              Control.Monad.Trans.Class.MonadTrans (Reader.ReaderT r_Xgr)))



[2 of 3] Compiling Eval2            ( Eval2.hs, build/Eval2.o )

==================== Tidy Core ====================
Result size of Tidy Core = {terms: 53, types: 99, coercions: 51}

Eval2.runEval2 :: GHC.Types.Int
[GblId,
 Caf=NoCafRefs,
 Str=DmdType m,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=False, Expandable=True,
         Guidance=IF_ARGS [] 10 20}]
Eval2.runEval2 = GHC.Types.I# 0

Eval2.runEval1
  :: forall void_j.
     Eval2.Eval void_j
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #)
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType LL,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=IF_ARGS [0 0] 56 0}]
Eval2.runEval1 =
  \ (@ void_j)
    (m_arb :: Eval2.Eval void_j)
    (eta_B1 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    case GHC.Prim.newMutVar#
           @ GHC.Types.Int @ GHC.Prim.RealWorld Eval2.runEval2 eta_B1
    of _ { (# ipv_atm, ipv1_atn #) ->
    let {
      a_stK :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
      [LclId, Str=DmdType m]
      a_stK =
        GHC.STRef.STRef @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_atn } in
    case (((m_arb
            `cast` (<Reader.NTCo:ReaderT
                       <(Eval2.Value, Eval2.Value)> <GHC.Types.IO> <void_j>>
                    :: Reader.ReaderT (Eval2.Value, Eval2.Value) GHC.Types.IO void_j
                         ~#
                       ((Eval2.Value, Eval2.Value) -> GHC.Types.IO void_j)))
             (a_stK
              `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int>
                      :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                           ~#
                         GHC.IORef.IORef GHC.Types.Int),
              a_stK
              `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int>
                      :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                           ~#
                         GHC.IORef.IORef GHC.Types.Int)))
          `cast` (<GHC.Types.NTCo:IO <void_j>>
                  :: GHC.Types.IO void_j
                       ~#
                     (GHC.Prim.State# GHC.Prim.RealWorld
                      -> (# GHC.Prim.State# GHC.Prim.RealWorld, void_j #))))
           ipv_atm
    of _ { (# ipv2_Xu8, _ #) ->
    GHC.Prim.readMutVar#
      @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_atn ipv2_Xu8
    }
    }

Eval2.runEval
  :: forall void_ar9.
     Eval2.Eval void_ar9 -> GHC.Types.IO GHC.Types.Int
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType LL,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval2.runEval =
  Eval2.runEval1
  `cast` (forall void_j.
          <Eval2.Eval void_j> -> Sym <(GHC.Types.NTCo:IO <GHC.Types.Int>)>
          :: (forall void_j.
              Eval2.Eval void_j
              -> GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #))
               ~#
             (forall void_j. Eval2.Eval void_j -> GHC.Types.IO GHC.Types.Int))

Eval2.ask3
  :: (Eval2.Value, Eval2.Value)
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval2.Value #)
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType LL,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval2.ask3 =
  \ (r_afu :: (Eval2.Value, Eval2.Value))
    (s_atC :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# s_atC, case r_afu of _ { (x_asR, ds1_asS) -> x_asR } #)

Eval2.ask1 :: Eval2.Eval Eval2.Value
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType LL,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval2.ask1 =
  Eval2.ask3
  `cast` ((<(Eval2.Value, Eval2.Value)>
           -> Sym <(GHC.Types.NTCo:IO <Eval2.Value>)>) ; Sym
                                                           <(Reader.NTCo:ReaderT
                                                               <(Eval2.Value, Eval2.Value)>
                                                               <GHC.Types.IO>
                                                               <Eval2.Value>)>
          :: ((Eval2.Value, Eval2.Value)
              -> GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval2.Value #))
               ~#
             Reader.ReaderT (Eval2.Value, Eval2.Value) GHC.Types.IO Eval2.Value)

Eval2.ask4
  :: (Eval2.Value, Eval2.Value)
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval2.Value #)
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType LL,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval2.ask4 =
  \ (r_Xg4 :: (Eval2.Value, Eval2.Value))
    (s_atC :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# s_atC, case r_Xg4 of _ { (ds1_asZ, y_at0) -> y_at0 } #)

Eval2.ask2 :: Eval2.Eval Eval2.Value
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType LL,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval2.ask2 =
  Eval2.ask4
  `cast` ((<(Eval2.Value, Eval2.Value)>
           -> Sym <(GHC.Types.NTCo:IO <Eval2.Value>)>) ; Sym
                                                           <(Reader.NTCo:ReaderT
                                                               <(Eval2.Value, Eval2.Value)>
                                                               <GHC.Types.IO>
                                                               <Eval2.Value>)>
          :: ((Eval2.Value, Eval2.Value)
              -> GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval2.Value #))
               ~#
             Reader.ReaderT (Eval2.Value, Eval2.Value) GHC.Types.IO Eval2.Value)



[3 of 3] Compiling OptimizeMonadTrans ( OptimizeMonadTrans.hs, build/OptimizeMonadTrans.o )

==================== Tidy Core ====================
Result size of Tidy Core = {terms: 172, types: 226, coercions: 74}

lvl_r10O :: GHC.Types.Int
[GblId, Caf=NoCafRefs]
lvl_r10O = GHC.Types.I# 1

a_r10P
  :: GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #)
[GblId, Arity=1, Caf=NoCafRefs, Str=DmdType L]
a_r10P =
  \ (s_XuC :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# s_XuC, lvl_r10O #)

a1_r10Q
  :: (Eval2.Value, Eval2.Value)
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #)
[GblId, Arity=2, Caf=NoCafRefs, Str=DmdType A]
a1_r10Q =
  \ _ (eta_B1 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# eta_B1, lvl_r10O #)

lvl1_r10R :: GHC.Types.Int
[GblId, Caf=NoCafRefs]
lvl1_r10R = GHC.Types.I# 2

a2_r10S
  :: GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #)
[GblId, Arity=1, Caf=NoCafRefs, Str=DmdType L]
a2_r10S =
  \ (s_XuL :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# s_XuL, lvl1_r10R #)

a3_r10T
  :: (Eval2.Value, Eval2.Value)
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #)
[GblId, Arity=2, Caf=NoCafRefs, Str=DmdType A]
a3_r10T =
  \ _ (eta_B1 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# eta_B1, lvl1_r10R #)

a4_r10U :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a4_r10U =
  GHC.Types.:
    @ OptimizeMonadTrans.Tree
    OptimizeMonadTrans.Leaf
    (GHC.Types.[] @ OptimizeMonadTrans.Tree)

a5_r10V :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a5_r10V =
  GHC.Types.:
    @ OptimizeMonadTrans.Tree OptimizeMonadTrans.Leaf a4_r10U

a6_r10W :: OptimizeMonadTrans.Tree
[GblId, Caf=NoCafRefs, Str=DmdType]
a6_r10W =
  OptimizeMonadTrans.Branch
    (a3_r10T
     `cast` ((<(Eval2.Value, Eval2.Value)>
              -> Sym <(GHC.Types.NTCo:IO <GHC.Types.Int>)>) ; Sym
                                                                <(Reader.NTCo:ReaderT
                                                                    <(Eval2.Value, Eval2.Value)>
                                                                    <GHC.Types.IO>
                                                                    <GHC.Types.Int>)>
             :: ((Eval2.Value, Eval2.Value)
                 -> GHC.Prim.State# GHC.Prim.RealWorld
                 -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #))
                  ~#
                Reader.ReaderT
                  (Eval2.Value, Eval2.Value) GHC.Types.IO GHC.Types.Int))
    a5_r10V

a7_r10X :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a7_r10X = GHC.Types.: @ OptimizeMonadTrans.Tree a6_r10W a4_r10U

tree_rxJ :: OptimizeMonadTrans.Tree
[GblId, Caf=NoCafRefs, Str=DmdType]
tree_rxJ =
  OptimizeMonadTrans.Branch
    (a1_r10Q
     `cast` ((<(Eval2.Value, Eval2.Value)>
              -> Sym <(GHC.Types.NTCo:IO <GHC.Types.Int>)>) ; Sym
                                                                <(Reader.NTCo:ReaderT
                                                                    <(Eval2.Value, Eval2.Value)>
                                                                    <GHC.Types.IO>
                                                                    <GHC.Types.Int>)>
             :: ((Eval2.Value, Eval2.Value)
                 -> GHC.Prim.State# GHC.Prim.RealWorld
                 -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #))
                  ~#
                Reader.ReaderT
                  (Eval2.Value, Eval2.Value) GHC.Types.IO GHC.Types.Int))
    a7_r10X

Rec {
a8_r10Y
  :: [OptimizeMonadTrans.Tree]
     -> (Eval2.Value, Eval2.Value)
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #)
[GblId, Arity=3, Caf=NoCafRefs, Str=DmdType SLL]
a8_r10Y =
  \ (ds_dG9 :: [OptimizeMonadTrans.Tree])
    (eta_B2 :: (Eval2.Value, Eval2.Value))
    (eta1_B1 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    case ds_dG9 of _ {
      [] -> (# eta1_B1, GHC.Tuple.() #);
      : x_aAs xs_aAt ->
        case x_aAs of _ {
          OptimizeMonadTrans.Branch action_aAv children_aAw ->
            case (((action_aAv
                    `cast` (<Reader.NTCo:ReaderT
                               <(Eval2.Value, Eval2.Value)> <GHC.Types.IO> <GHC.Types.Int>>
                            :: Reader.ReaderT
                                 (Eval2.Value, Eval2.Value) GHC.Types.IO GHC.Types.Int
                                 ~#
                               ((Eval2.Value, Eval2.Value) -> GHC.Types.IO GHC.Types.Int)))
                     eta_B2)
                  `cast` (<GHC.Types.NTCo:IO <GHC.Types.Int>>
                          :: GHC.Types.IO GHC.Types.Int
                               ~#
                             (GHC.Prim.State# GHC.Prim.RealWorld
                              -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #))))
                   eta1_B1
            of _ { (# ipv_atF, ipv1_atG #) ->
            case eta_B2 of wild2_asP { (x1_asR, ds2_asS) ->
            case x1_asR
                 `cast` (<GHC.IORef.NTCo:IORef> <GHC.Types.Int>
                         :: GHC.IORef.IORef GHC.Types.Int
                              ~#
                            GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int)
            of _ { GHC.STRef.STRef var#_atR ->
            case GHC.Prim.readMutVar#
                   @ GHC.Prim.RealWorld @ GHC.Types.Int var#_atR ipv_atF
            of _ { (# ipv2_Xus, ipv3_Xuu #) ->
            case ipv1_atG of _ { GHC.Types.I# x2_aHE ->
            case ipv3_Xuu of _ { GHC.Types.I# y_aHI ->
            case GHC.Prim.writeMutVar#
                   @ GHC.Prim.RealWorld
                   @ GHC.Types.Int
                   var#_atR
                   (GHC.Types.I# (GHC.Prim.+# x2_aHE y_aHI))
                   ipv2_Xus
            of s2#_aJn { __DEFAULT ->
            a8_r10Y
              (GHC.Base.++ @ OptimizeMonadTrans.Tree children_aAw xs_aAt)
              wild2_asP
              s2#_aJn
            }
            }
            }
            }
            }
            }
            };
          OptimizeMonadTrans.Leaf ->
            case eta_B2 of wild2_asX { (ds1_asZ, y_at0) ->
            case y_at0
                 `cast` (<GHC.IORef.NTCo:IORef> <GHC.Types.Int>
                         :: GHC.IORef.IORef GHC.Types.Int
                              ~#
                            GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int)
            of _ { GHC.STRef.STRef var#_atR ->
            case GHC.Prim.readMutVar#
                   @ GHC.Prim.RealWorld @ GHC.Types.Int var#_atR eta1_B1
            of _ { (# ipv_atF, ipv1_atG #) ->
            case ipv1_atG of _ { GHC.Types.I# x1_aHE ->
            case GHC.Prim.writeMutVar#
                   @ GHC.Prim.RealWorld
                   @ GHC.Types.Int
                   var#_atR
                   (GHC.Types.I# (GHC.Prim.+# x1_aHE 1))
                   ipv_atF
            of s2#_aJn { __DEFAULT ->
            a8_r10Y xs_aAt wild2_asX s2#_aJn
            }
            }
            }
            }
            }
        }
    }
end Rec }

a9_r10Z :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a9_r10Z =
  GHC.Types.:
    @ OptimizeMonadTrans.Tree
    tree_rxJ
    (GHC.Types.[] @ OptimizeMonadTrans.Tree)

a10_r110
  :: (Eval2.Value, Eval2.Value)
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #)
[GblId, Arity=2, Str=DmdType]
a10_r110 = a8_r10Y a9_r10Z

OptimizeMonadTrans.example [InlPrag=NOINLINE] :: Eval2.Eval ()
[GblId, Str=DmdType]
OptimizeMonadTrans.example =
  a10_r110
  `cast` ((<(Eval2.Value, Eval2.Value)>
           -> Sym <(GHC.Types.NTCo:IO <()>)>) ; Sym
                                                  <(Reader.NTCo:ReaderT
                                                      <(Eval2.Value, Eval2.Value)>
                                                      <GHC.Types.IO>
                                                      <()>)>
          :: ((Eval2.Value, Eval2.Value)
              -> GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #))
               ~#
             Reader.ReaderT (Eval2.Value, Eval2.Value) GHC.Types.IO ())

OptimizeMonadTrans.main1
  :: GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #)
[GblId,
 Arity=1,
 Str=DmdType L,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=1, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=IF_ARGS [0] 126 0}]
OptimizeMonadTrans.main1 =
  \ (s_atC :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    case GHC.Prim.newMutVar#
           @ GHC.Types.Int @ GHC.Prim.RealWorld Eval2.runEval2 s_atC
    of _ { (# ipv_atm, ipv1_atn #) ->
    let {
      a11_stK :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
      [LclId, Str=DmdType m]
      a11_stK =
        GHC.STRef.STRef @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_atn } in
    case (((OptimizeMonadTrans.example
            `cast` (<Reader.NTCo:ReaderT
                       <(Eval2.Value, Eval2.Value)> <GHC.Types.IO> <()>>
                    :: Reader.ReaderT (Eval2.Value, Eval2.Value) GHC.Types.IO ()
                         ~#
                       ((Eval2.Value, Eval2.Value) -> GHC.Types.IO ())))
             (a11_stK
              `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int>
                      :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                           ~#
                         GHC.IORef.IORef GHC.Types.Int),
              a11_stK
              `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int>
                      :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                           ~#
                         GHC.IORef.IORef GHC.Types.Int)))
          `cast` (<GHC.Types.NTCo:IO <()>>
                  :: GHC.Types.IO ()
                       ~#
                     (GHC.Prim.State# GHC.Prim.RealWorld
                      -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #))))
           ipv_atm
    of _ { (# ipv2_Xu8, _ #) ->
    case GHC.Prim.readMutVar#
           @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_atn ipv2_Xu8
    of _ { (# ipv4_atF, ipv5_atG #) ->
    GHC.IO.Handle.Text.hPutStr2
      GHC.IO.Handle.FD.stdout
      (GHC.Show.$fShowInt_$cshow ipv5_atG)
      GHC.Types.True
      ipv4_atF
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



