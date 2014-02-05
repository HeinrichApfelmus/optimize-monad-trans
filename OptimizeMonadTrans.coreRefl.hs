[1 of 3] Compiling ReaderReflection ( ReaderReflection.hs, build/ReaderReflection.o )

==================== Tidy Core ====================
Result size of Tidy Core = {terms: 295, types: 901, coercions: 541}

ReaderReflection.unT1
  :: forall r_i s_j (m_k :: * -> *) a_l.
     ReaderReflection.Tag r_i s_j m_k a_l
     -> ReaderReflection.Tag r_i s_j m_k a_l
[GblId,
 Arity=1,
 Caf=NoCafRefs,
 Str=DmdType S,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=1, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
ReaderReflection.unT1 =
  \ (@ r_i)
    (@ s_j)
    (@ (m_k :: * -> *))
    (@ a_l)
    (ds_dso :: ReaderReflection.Tag r_i s_j m_k a_l) ->
    ds_dso

ReaderReflection.unT
  :: forall r_anz s_anA (m_anB :: * -> *) a_anC.
     ReaderReflection.Tag r_anz s_anA m_anB a_anC -> m_anB a_anC
[GblId[[RecSel]],
 Arity=1,
 Caf=NoCafRefs,
 Str=DmdType S,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
ReaderReflection.unT =
  ReaderReflection.unT1
  `cast` (forall r_i s_j (m_k :: * -> *) a_l.
          <ReaderReflection.Tag r_i s_j m_k a_l>
          -> <ReaderReflection.NTCo:Tag <r_i> <s_j> <m_k>> <a_l>
          :: (forall r_i s_j (m_k :: * -> *) a_l.
              ReaderReflection.Tag r_i s_j m_k a_l
              -> ReaderReflection.Tag r_i s_j m_k a_l)
               ~#
             (forall r_i s_j (m_k :: * -> *) a_l.
              ReaderReflection.Tag r_i s_j m_k a_l -> m_k a_l))

ReaderReflection.run
  :: forall r_anv (m_anw :: * -> *) a_anx s_any.
     Data.Reflection.Reifies * s_any r_anv =>
     ReaderReflection.ReaderT r_anv m_anw a_anx
     -> ReaderReflection.Tag r_anv s_any m_anw a_anx
[GblId[[RecSel]],
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType LC(S),
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
ReaderReflection.run =
  \ (@ r_x)
    (@ (m_y :: * -> *))
    (@ a_z)
    (@ s_tq)
    ($dReifies_aoE :: Data.Reflection.Reifies * s_tq r_x)
    (ds_dsm :: ReaderReflection.ReaderT r_x m_y a_z) ->
    (ds_dsm
     `cast` (<ReaderReflection.NTCo:ReaderT <r_x> <m_y> <a_z>>
             :: ReaderReflection.ReaderT r_x m_y a_z
                  ~#
                (forall s_any.
                 Data.Reflection.Reifies * s_any r_x =>
                 ReaderReflection.Tag r_x s_any m_y a_z)))
      @ s_tq $dReifies_aoE

ReaderReflection.ask1
  :: forall r_t18 (m_t19 :: * -> *).
     GHC.Base.Monad m_t19 =>
     forall s_apC. Data.Reflection.Reifies * s_apC r_t18 => m_t19 r_t18
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType U(AASA)L,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=False)
         Tmpl= \ (@ r_t18)
                 (@ (m_t19 :: * -> *))
                 ($dMonad_app [Occ=Once] :: GHC.Base.Monad m_t19)
                 (@ s_apC)
                 ($dReifies_apD [Occ=Once]
                    :: Data.Reflection.Reifies * s_apC r_t18) ->
                 GHC.Base.return
                   @ m_t19
                   $dMonad_app
                   @ r_t18
                   (($dReifies_apD
                     `cast` (<Data.Reflection.NTCo:Reifies <*> <s_apC> <r_t18>>
                             :: Data.Reflection.Reifies * s_apC r_t18
                                  ~#
                                (forall (proxy_apx :: * -> *). proxy_apx s_apC -> r_t18)))
                      @ (Data.Proxy.Proxy *) (Data.Proxy.Proxy @ * @ s_apC))}]
ReaderReflection.ask1 =
  \ (@ r_t18)
    (@ (m_t19 :: * -> *))
    ($dMonad_app :: GHC.Base.Monad m_t19)
    (@ s_apC)
    ($dReifies_apD :: Data.Reflection.Reifies * s_apC r_t18) ->
    GHC.Base.return
      @ m_t19
      $dMonad_app
      @ r_t18
      (($dReifies_apD
        `cast` (<Data.Reflection.NTCo:Reifies <*> <s_apC> <r_t18>>
                :: Data.Reflection.Reifies * s_apC r_t18
                     ~#
                   (forall (proxy_apx :: * -> *). proxy_apx s_apC -> r_t18)))
         @ (Data.Proxy.Proxy *) (Data.Proxy.Proxy @ * @ s_apC))

ReaderReflection.ask
  :: forall r_anK (m_anL :: * -> *).
     GHC.Base.Monad m_anL =>
     ReaderReflection.ReaderT r_anK m_anL r_anK
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType U(AASA)L,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= ReaderReflection.ask1
               `cast` (forall r_t18 (m_t19 :: * -> *).
                       <GHC.Base.Monad m_t19>
                       -> (forall s_apC.
                           <Data.Reflection.Reifies * s_apC r_t18>
                           -> Sym
                                <(ReaderReflection.NTCo:Tag
                                    <r_t18> <s_apC> <m_t19>)> <r_t18>) ; Sym
                                                                           <(ReaderReflection.NTCo:ReaderT
                                                                               <r_t18>
                                                                               <m_t19>
                                                                               <r_t18>)>
                       :: (forall r_t18 (m_t19 :: * -> *).
                           GHC.Base.Monad m_t19 =>
                           forall s_apC. Data.Reflection.Reifies * s_apC r_t18 => m_t19 r_t18)
                            ~#
                          (forall r_t18 (m_t19 :: * -> *).
                           GHC.Base.Monad m_t19 =>
                           ReaderReflection.ReaderT r_t18 m_t19 r_t18))}]
ReaderReflection.ask =
  ReaderReflection.ask1
  `cast` (forall r_t18 (m_t19 :: * -> *).
          <GHC.Base.Monad m_t19>
          -> (forall s_apC.
              <Data.Reflection.Reifies * s_apC r_t18>
              -> Sym
                   <(ReaderReflection.NTCo:Tag
                       <r_t18> <s_apC> <m_t19>)> <r_t18>) ; Sym
                                                              <(ReaderReflection.NTCo:ReaderT
                                                                  <r_t18> <m_t19> <r_t18>)>
          :: (forall r_t18 (m_t19 :: * -> *).
              GHC.Base.Monad m_t19 =>
              forall s_apC. Data.Reflection.Reifies * s_apC r_t18 => m_t19 r_t18)
               ~#
             (forall r_t18 (m_t19 :: * -> *).
              GHC.Base.Monad m_t19 =>
              ReaderReflection.ReaderT r_t18 m_t19 r_t18))

ReaderReflection.runReaderT
  :: forall r_ao0 (m_ao1 :: * -> *) a_ao2.
     ReaderReflection.ReaderT r_ao0 m_ao1 a_ao2 -> r_ao0 -> m_ao1 a_ao2
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType C(S)L,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=IF_ARGS [0 0] 33 60}]
ReaderReflection.runReaderT =
  \ (@ r_t1U)
    (@ (m_t1V :: * -> *))
    (@ a_t1W)
    (ds_dsl :: ReaderReflection.ReaderT r_t1U m_t1V a_t1W)
    (r_ao4 :: r_t1U) ->
    ((\ (@ s_aqo)
        ($dReifies_aqp :: Data.Reflection.Reifies * s_aqo r_t1U)
        _ ->
        (ds_dsl
         `cast` (<ReaderReflection.NTCo:ReaderT <r_t1U> <m_t1V> <a_t1W>>
                 :: ReaderReflection.ReaderT r_t1U m_t1V a_t1W
                      ~#
                    (forall s_any.
                     Data.Reflection.Reifies * s_any r_t1U =>
                     ReaderReflection.Tag r_t1U s_any m_t1V a_t1W)))
          @ s_aqo $dReifies_aqp)
     `cast` ((forall s_aqo.
              <Data.Reflection.Reifies * s_aqo r_t1U>
              -> <Data.Proxy.Proxy * s_aqo>
              -> <ReaderReflection.NTCo:Tag
                    <r_t1U> <s_aqo> <m_t1V>> <a_t1W>) ; (Sym
                                                           <(Data.Reflection.NTCo:Magic
                                                               <r_t1U> <m_t1V a_t1W>)> ; UnsafeCo
                                                                                           (Data.Reflection.Magic
                                                                                              r_t1U
                                                                                              (m_t1V a_t1W))
                                                                                           ((GHC.Prim.Any
                                                                                               *
                                                                                             -> r_t1U)
                                                                                            -> Data.Proxy.Proxy
                                                                                                 AnyK
                                                                                                 (GHC.Prim.Any
                                                                                                    AnyK)
                                                                                            -> m_t1V a_t1W))
             :: (forall s_aqo.
                 Data.Reflection.Reifies * s_aqo r_t1U =>
                 Data.Proxy.Proxy * s_aqo
                 -> ReaderReflection.Tag r_t1U s_aqo m_t1V a_t1W)
                  ~#
                ((GHC.Prim.Any * -> r_t1U)
                 -> Data.Proxy.Proxy AnyK (GHC.Prim.Any AnyK) -> m_t1V a_t1W)))
      (\ _ -> r_ao4) (Data.Proxy.Proxy @ AnyK @ (GHC.Prim.Any AnyK))

ReaderReflection.$fMonadTag1
  :: forall r_aop s_aoq (m_aor :: * -> *).
     GHC.Base.Monad m_aor =>
     forall a_t47. a_t47 -> m_aor a_t47
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType U(AASA)L,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_aop)
                 (@ s_aoq)
                 (@ (m_aor :: * -> *))
                 ($dMonad_arb [Occ=Once] :: GHC.Base.Monad m_aor)
                 (@ a_t47)
                 (a2_aos [Occ=Once] :: a_t47) ->
                 GHC.Base.return @ m_aor $dMonad_arb @ a_t47 a2_aos}]
ReaderReflection.$fMonadTag1 =
  \ (@ r_aop)
    (@ s_aoq)
    (@ (m_aor :: * -> *))
    ($dMonad_arb :: GHC.Base.Monad m_aor)
    (@ a_t47)
    (a2_aos :: a_t47) ->
    GHC.Base.return @ m_aor $dMonad_arb @ a_t47 a2_aos

ReaderReflection.$fMonadTag_$creturn
  :: forall r_aop s_aoq (m_aor :: * -> *).
     GHC.Base.Monad m_aor =>
     forall a_apu. a_apu -> ReaderReflection.Tag r_aop s_aoq m_aor a_apu
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType U(AASA)L,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= ReaderReflection.$fMonadTag1
               `cast` (forall r_aop s_aoq (m_aor :: * -> *).
                       <GHC.Base.Monad m_aor>
                       -> forall a_t47.
                          <a_t47>
                          -> Sym
                               <(ReaderReflection.NTCo:Tag <r_aop> <s_aoq> <m_aor>)> <a_t47>
                       :: (forall r_aop s_aoq (m_aor :: * -> *).
                           GHC.Base.Monad m_aor =>
                           forall a_t47. a_t47 -> m_aor a_t47)
                            ~#
                          (forall r_aop s_aoq (m_aor :: * -> *).
                           GHC.Base.Monad m_aor =>
                           forall a_t47.
                           a_t47 -> ReaderReflection.Tag r_aop s_aoq m_aor a_t47))}]
ReaderReflection.$fMonadTag_$creturn =
  ReaderReflection.$fMonadTag1
  `cast` (forall r_aop s_aoq (m_aor :: * -> *).
          <GHC.Base.Monad m_aor>
          -> forall a_t47.
             <a_t47>
             -> Sym
                  <(ReaderReflection.NTCo:Tag <r_aop> <s_aoq> <m_aor>)> <a_t47>
          :: (forall r_aop s_aoq (m_aor :: * -> *).
              GHC.Base.Monad m_aor =>
              forall a_t47. a_t47 -> m_aor a_t47)
               ~#
             (forall r_aop s_aoq (m_aor :: * -> *).
              GHC.Base.Monad m_aor =>
              forall a_t47.
              a_t47 -> ReaderReflection.Tag r_aop s_aoq m_aor a_t47))

ReaderReflection.$fMonadTag2
  :: forall r_Xpg s_Xpi (m_Xpk :: * -> *).
     GHC.Base.Monad m_Xpk =>
     forall a_t3L b_t3M.
     ReaderReflection.Tag r_Xpg s_Xpi m_Xpk a_t3L
     -> (a_t3L -> ReaderReflection.Tag r_Xpg s_Xpi m_Xpk b_t3M)
     -> m_Xpk b_t3M
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType U(SAAA)LL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=False)
         Tmpl= \ (@ r_Xpg)
                 (@ s_Xpi)
                 (@ (m_Xpk :: * -> *))
                 ($dMonad_Xs5 [Occ=Once] :: GHC.Base.Monad m_Xpk)
                 (@ a_t3L)
                 (@ b_t3M)
                 (m_aot [Occ=Once] :: ReaderReflection.Tag r_Xpg s_Xpi m_Xpk a_t3L)
                 (k_aou [Occ=OnceL!]
                    :: a_t3L -> ReaderReflection.Tag r_Xpg s_Xpi m_Xpk b_t3M) ->
                 GHC.Base.>>=
                   @ m_Xpk
                   $dMonad_Xs5
                   @ a_t3L
                   @ b_t3M
                   (m_aot
                    `cast` (<ReaderReflection.NTCo:Tag <r_Xpg> <s_Xpi> <m_Xpk>> <a_t3L>
                            :: ReaderReflection.Tag r_Xpg s_Xpi m_Xpk a_t3L ~# m_Xpk a_t3L))
                   ((\ (x_at0 [Occ=Once] :: a_t3L) -> k_aou x_at0)
                    `cast` (<a_t3L>
                            -> <ReaderReflection.NTCo:Tag <r_Xpg> <s_Xpi> <m_Xpk>> <b_t3M>
                            :: (a_t3L -> ReaderReflection.Tag r_Xpg s_Xpi m_Xpk b_t3M)
                                 ~#
                               (a_t3L -> m_Xpk b_t3M)))}]
ReaderReflection.$fMonadTag2 =
  \ (@ r_Xpg)
    (@ s_Xpi)
    (@ (m_Xpk :: * -> *))
    ($dMonad_Xs5 :: GHC.Base.Monad m_Xpk)
    (@ a_t3L)
    (@ b_t3M)
    (m_aot :: ReaderReflection.Tag r_Xpg s_Xpi m_Xpk a_t3L)
    (k_aou :: a_t3L -> ReaderReflection.Tag r_Xpg s_Xpi m_Xpk b_t3M) ->
    GHC.Base.>>=
      @ m_Xpk
      $dMonad_Xs5
      @ a_t3L
      @ b_t3M
      (m_aot
       `cast` (<ReaderReflection.NTCo:Tag <r_Xpg> <s_Xpi> <m_Xpk>> <a_t3L>
               :: ReaderReflection.Tag r_Xpg s_Xpi m_Xpk a_t3L ~# m_Xpk a_t3L))
      ((\ (x_at0 :: a_t3L) -> k_aou x_at0)
       `cast` (<a_t3L>
               -> <ReaderReflection.NTCo:Tag <r_Xpg> <s_Xpi> <m_Xpk>> <b_t3M>
               :: (a_t3L -> ReaderReflection.Tag r_Xpg s_Xpi m_Xpk b_t3M)
                    ~#
                  (a_t3L -> m_Xpk b_t3M)))

ReaderReflection.$fMonadTag_$c>>=
  :: forall r_aop s_aoq (m_aor :: * -> *).
     GHC.Base.Monad m_aor =>
     forall a_apW b_apX.
     ReaderReflection.Tag r_aop s_aoq m_aor a_apW
     -> (a_apW -> ReaderReflection.Tag r_aop s_aoq m_aor b_apX)
     -> ReaderReflection.Tag r_aop s_aoq m_aor b_apX
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType U(SAAA)LL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= ReaderReflection.$fMonadTag2
               `cast` (forall r_Xpg s_Xpi (m_Xpk :: * -> *).
                       <GHC.Base.Monad m_Xpk>
                       -> forall a_t3L b_t3M.
                          <ReaderReflection.Tag r_Xpg s_Xpi m_Xpk a_t3L>
                          -> <a_t3L -> ReaderReflection.Tag r_Xpg s_Xpi m_Xpk b_t3M>
                          -> Sym
                               <(ReaderReflection.NTCo:Tag <r_Xpg> <s_Xpi> <m_Xpk>)> <b_t3M>
                       :: (forall r_Xpg s_Xpi (m_Xpk :: * -> *).
                           GHC.Base.Monad m_Xpk =>
                           forall a_t3L b_t3M.
                           ReaderReflection.Tag r_Xpg s_Xpi m_Xpk a_t3L
                           -> (a_t3L -> ReaderReflection.Tag r_Xpg s_Xpi m_Xpk b_t3M)
                           -> m_Xpk b_t3M)
                            ~#
                          (forall r_Xpg s_Xpi (m_Xpk :: * -> *).
                           GHC.Base.Monad m_Xpk =>
                           forall a_t3L b_t3M.
                           ReaderReflection.Tag r_Xpg s_Xpi m_Xpk a_t3L
                           -> (a_t3L -> ReaderReflection.Tag r_Xpg s_Xpi m_Xpk b_t3M)
                           -> ReaderReflection.Tag r_Xpg s_Xpi m_Xpk b_t3M))}]
ReaderReflection.$fMonadTag_$c>>= =
  ReaderReflection.$fMonadTag2
  `cast` (forall r_Xpg s_Xpi (m_Xpk :: * -> *).
          <GHC.Base.Monad m_Xpk>
          -> forall a_t3L b_t3M.
             <ReaderReflection.Tag r_Xpg s_Xpi m_Xpk a_t3L>
             -> <a_t3L -> ReaderReflection.Tag r_Xpg s_Xpi m_Xpk b_t3M>
             -> Sym
                  <(ReaderReflection.NTCo:Tag <r_Xpg> <s_Xpi> <m_Xpk>)> <b_t3M>
          :: (forall r_Xpg s_Xpi (m_Xpk :: * -> *).
              GHC.Base.Monad m_Xpk =>
              forall a_t3L b_t3M.
              ReaderReflection.Tag r_Xpg s_Xpi m_Xpk a_t3L
              -> (a_t3L -> ReaderReflection.Tag r_Xpg s_Xpi m_Xpk b_t3M)
              -> m_Xpk b_t3M)
               ~#
             (forall r_Xpg s_Xpi (m_Xpk :: * -> *).
              GHC.Base.Monad m_Xpk =>
              forall a_t3L b_t3M.
              ReaderReflection.Tag r_Xpg s_Xpi m_Xpk a_t3L
              -> (a_t3L -> ReaderReflection.Tag r_Xpg s_Xpi m_Xpk b_t3M)
              -> ReaderReflection.Tag r_Xpg s_Xpi m_Xpk b_t3M))

ReaderReflection.$fMonadTag_$cfail
  :: forall r_aop s_aoq (m_aor :: * -> *).
     GHC.Base.Monad m_aor =>
     forall a_ar7.
     GHC.Base.String -> ReaderReflection.Tag r_aop s_aoq m_aor a_ar7
[GblId,
 Arity=2,
 Str=DmdType ASb,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_Xps)
                 (@ s_Xpu)
                 (@ (m_Xpw :: * -> *))
                 _
                 (@ a_atc)
                 (eta_B1 [Occ=Once] :: [GHC.Types.Char]) ->
                 GHC.Err.error
                   @ (ReaderReflection.Tag r_Xps s_Xpu m_Xpw a_atc) eta_B1}]
ReaderReflection.$fMonadTag_$cfail =
  \ (@ r_Xps)
    (@ s_Xpu)
    (@ (m_Xpw :: * -> *))
    _
    (@ a_atc)
    (eta_B1 :: [GHC.Types.Char]) ->
    GHC.Err.error
      @ (ReaderReflection.Tag r_Xps s_Xpu m_Xpw a_atc) eta_B1

a_ruO
  :: forall r_Xpr s_Xpt (m_Xpv :: * -> *).
     GHC.Base.Monad m_Xpv =>
     forall a_aqT b_aqU.
     ReaderReflection.Tag r_Xpr s_Xpt m_Xpv a_aqT
     -> ReaderReflection.Tag r_Xpr s_Xpt m_Xpv b_aqU -> m_Xpv b_aqU
[GblId, Arity=3, Caf=NoCafRefs, Str=DmdType U(SAAA)LL]
a_ruO =
  \ (@ r_Xpr)
    (@ s_Xpt)
    (@ (m_Xpv :: * -> *))
    ($dMonad_Xsg :: GHC.Base.Monad m_Xpv)
    (@ a_aqT)
    (@ b_aqU)
    (eta_B2 :: ReaderReflection.Tag r_Xpr s_Xpt m_Xpv a_aqT)
    (eta1_B1 :: ReaderReflection.Tag r_Xpr s_Xpt m_Xpv b_aqU) ->
    GHC.Base.>>=
      @ m_Xpv
      $dMonad_Xsg
      @ a_aqT
      @ b_aqU
      (eta_B2
       `cast` (<ReaderReflection.NTCo:Tag <r_Xpr> <s_Xpt> <m_Xpv>> <a_aqT>
               :: ReaderReflection.Tag r_Xpr s_Xpt m_Xpv a_aqT ~# m_Xpv a_aqT))
      ((\ _ -> eta1_B1)
       `cast` (<a_aqT>
               -> <ReaderReflection.NTCo:Tag <r_Xpr> <s_Xpt> <m_Xpv>> <b_aqU>
               :: (a_aqT -> ReaderReflection.Tag r_Xpr s_Xpt m_Xpv b_aqU)
                    ~#
                  (a_aqT -> m_Xpv b_aqU)))

ReaderReflection.$fMonadTag_$c>> [InlPrag=INLINE (sat-args=2)]
  :: forall r_aop s_aoq (m_aor :: * -> *).
     GHC.Base.Monad m_aor =>
     forall a_aqT b_aqU.
     ReaderReflection.Tag r_aop s_aoq m_aor a_aqT
     -> ReaderReflection.Tag r_aop s_aoq m_aor b_aqU
     -> ReaderReflection.Tag r_aop s_aoq m_aor b_aqU
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType U(SAAA)LL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=False,boring_ok=False)
         Tmpl= \ (@ r_Xqe)
                 (@ s_Xqh)
                 (@ (m_Xqk :: * -> *))
                 ($dMonad_Xt6 [Occ=Once] :: GHC.Base.Monad m_Xqk)
                 (@ a_at5)
                 (@ b_at6)
                 (m_at7 [Occ=Once] :: ReaderReflection.Tag r_Xqe s_Xqh m_Xqk a_at5)
                 (k_at8 [Occ=OnceL]
                    :: ReaderReflection.Tag r_Xqe s_Xqh m_Xqk b_at6) ->
                 ReaderReflection.$fMonadTag_$c>>=
                   @ r_Xqe
                   @ s_Xqh
                   @ m_Xqk
                   $dMonad_Xt6
                   @ a_at5
                   @ b_at6
                   m_at7
                   (\ _ -> k_at8)}]
ReaderReflection.$fMonadTag_$c>> =
  a_ruO
  `cast` (forall r_Xpr s_Xpt (m_Xpv :: * -> *).
          <GHC.Base.Monad m_Xpv>
          -> forall a_aqT b_aqU.
             <ReaderReflection.Tag r_Xpr s_Xpt m_Xpv a_aqT>
             -> <ReaderReflection.Tag r_Xpr s_Xpt m_Xpv b_aqU>
             -> Sym
                  <(ReaderReflection.NTCo:Tag <r_Xpr> <s_Xpt> <m_Xpv>)> <b_aqU>
          :: (forall r_Xpr s_Xpt (m_Xpv :: * -> *).
              GHC.Base.Monad m_Xpv =>
              forall a_aqT b_aqU.
              ReaderReflection.Tag r_Xpr s_Xpt m_Xpv a_aqT
              -> ReaderReflection.Tag r_Xpr s_Xpt m_Xpv b_aqU -> m_Xpv b_aqU)
               ~#
             (forall r_Xpr s_Xpt (m_Xpv :: * -> *).
              GHC.Base.Monad m_Xpv =>
              forall a_aqT b_aqU.
              ReaderReflection.Tag r_Xpr s_Xpt m_Xpv a_aqT
              -> ReaderReflection.Tag r_Xpr s_Xpt m_Xpv b_aqU
              -> ReaderReflection.Tag r_Xpr s_Xpt m_Xpv b_aqU))

lvl_ruP
  :: forall r_Xpq s_Xps (m_Xpu :: * -> *) a_atc.
     [GHC.Types.Char] -> ReaderReflection.Tag r_Xpq s_Xps m_Xpu a_atc
[GblId, Arity=1, Str=DmdType Tb]
lvl_ruP =
  \ (@ r_Xpq)
    (@ s_Xps)
    (@ (m_Xpu :: * -> *))
    (@ a_atc)
    (eta_XU :: [GHC.Types.Char]) ->
    GHC.Err.error
      @ (ReaderReflection.Tag r_Xpq s_Xps m_Xpu a_atc) eta_XU

ReaderReflection.$fMonadTag [InlPrag=[ALWAYS] CONLIKE]
  :: forall r_aop s_aoq (m_aor :: * -> *).
     GHC.Base.Monad m_aor =>
     GHC.Base.Monad (ReaderReflection.Tag r_aop s_aoq m_aor)
[GblId[DFunId],
 Arity=1,
 Str=DmdType Lm,
 Unf=DFun(arity=4) GHC.Base.D:Monad [{ReaderReflection.$fMonadTag_$c>>=},
                                     {ReaderReflection.$fMonadTag_$c>>},
                                     {ReaderReflection.$fMonadTag_$creturn},
                                     {ReaderReflection.$fMonadTag_$cfail}]]
ReaderReflection.$fMonadTag =
  \ (@ r_Xpq)
    (@ s_Xps)
    (@ (m_Xpu :: * -> *))
    ($dMonad_Xsf :: GHC.Base.Monad m_Xpu) ->
    let {
      lvl2_suE :: forall a_t47. a_t47 -> m_Xpu a_t47
      [LclId]
      lvl2_suE =
        \ (@ a_t47) -> GHC.Base.return @ m_Xpu $dMonad_Xsf @ a_t47 } in
    GHC.Base.D:Monad
      @ (ReaderReflection.Tag r_Xpq s_Xps m_Xpu)
      ((ReaderReflection.$fMonadTag2 @ r_Xpq @ s_Xps @ m_Xpu $dMonad_Xsf)
       `cast` (forall a_t3L b_t3M.
               <ReaderReflection.Tag r_Xpq s_Xps m_Xpu a_t3L>
               -> <a_t3L -> ReaderReflection.Tag r_Xpq s_Xps m_Xpu b_t3M>
               -> Sym
                    <(ReaderReflection.NTCo:Tag <r_Xpq> <s_Xps> <m_Xpu>)> <b_t3M>
               :: (forall a_t3L b_t3M.
                   ReaderReflection.Tag r_Xpq s_Xps m_Xpu a_t3L
                   -> (a_t3L -> ReaderReflection.Tag r_Xpq s_Xps m_Xpu b_t3M)
                   -> m_Xpu b_t3M)
                    ~#
                  (forall a_t3L b_t3M.
                   ReaderReflection.Tag r_Xpq s_Xps m_Xpu a_t3L
                   -> (a_t3L -> ReaderReflection.Tag r_Xpq s_Xps m_Xpu b_t3M)
                   -> ReaderReflection.Tag r_Xpq s_Xps m_Xpu b_t3M)))
      (ReaderReflection.$fMonadTag_$c>>
         @ r_Xpq @ s_Xps @ m_Xpu $dMonad_Xsf)
      ((\ (@ a_t47) (a2_aos :: a_t47) -> lvl2_suE @ a_t47 a2_aos)
       `cast` (forall a_t47.
               <a_t47>
               -> Sym
                    <(ReaderReflection.NTCo:Tag <r_Xpq> <s_Xps> <m_Xpu>)> <a_t47>
               :: (forall a_t47. a_t47 -> m_Xpu a_t47)
                    ~#
                  (forall a_t47.
                   a_t47 -> ReaderReflection.Tag r_Xpq s_Xps m_Xpu a_t47)))
      (lvl_ruP @ r_Xpq @ s_Xps @ m_Xpu)

ReaderReflection.$fMonadReaderT1
  :: forall r_aon (m_aoo :: * -> *).
     GHC.Base.Monad m_aoo =>
     forall a_t3G.
     a_t3G
     -> forall s_apL.
        Data.Reflection.Reifies * s_apL r_aon =>
        m_aoo a_t3G
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType U(AASA)LA,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_aon)
                 (@ (m_aoo :: * -> *))
                 ($dMonad_aqJ [Occ=Once] :: GHC.Base.Monad m_aoo)
                 (@ a_t3G)
                 (a2_aob [Occ=Once] :: a_t3G)
                 (@ s_apL)
                 _ ->
                 GHC.Base.return @ m_aoo $dMonad_aqJ @ a_t3G a2_aob}]
ReaderReflection.$fMonadReaderT1 =
  \ (@ r_aon)
    (@ (m_aoo :: * -> *))
    ($dMonad_aqJ :: GHC.Base.Monad m_aoo)
    (@ a_t3G)
    (a2_aob :: a_t3G)
    (@ s_apL)
    _ ->
    GHC.Base.return @ m_aoo $dMonad_aqJ @ a_t3G a2_aob

ReaderReflection.$fMonadReaderT_$creturn
  :: forall r_aon (m_aoo :: * -> *).
     GHC.Base.Monad m_aoo =>
     forall a_apu. a_apu -> ReaderReflection.ReaderT r_aon m_aoo a_apu
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType U(AASA)LA,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= ReaderReflection.$fMonadReaderT1
               `cast` (forall r_Xph (m_Xpj :: * -> *).
                       <GHC.Base.Monad m_Xpj>
                       -> forall a_X4C.
                          <a_X4C>
                          -> (forall s_XqI.
                              <Data.Reflection.Reifies * s_XqI r_Xph>
                              -> Sym
                                   <(ReaderReflection.NTCo:Tag
                                       <r_Xph> <s_XqI> <m_Xpj>)> <a_X4C>) ; Sym
                                                                              <(ReaderReflection.NTCo:ReaderT
                                                                                  <r_Xph>
                                                                                  <m_Xpj>
                                                                                  <a_X4C>)>
                       :: (forall r_Xph (m_Xpj :: * -> *).
                           GHC.Base.Monad m_Xpj =>
                           forall a_X4C.
                           a_X4C
                           -> forall s_XqI.
                              Data.Reflection.Reifies * s_XqI r_Xph =>
                              m_Xpj a_X4C)
                            ~#
                          (forall r_Xph (m_Xpj :: * -> *).
                           GHC.Base.Monad m_Xpj =>
                           forall a_X4C.
                           a_X4C -> ReaderReflection.ReaderT r_Xph m_Xpj a_X4C))}]
ReaderReflection.$fMonadReaderT_$creturn =
  ReaderReflection.$fMonadReaderT1
  `cast` (forall r_Xph (m_Xpj :: * -> *).
          <GHC.Base.Monad m_Xpj>
          -> forall a_X4C.
             <a_X4C>
             -> (forall s_XqI.
                 <Data.Reflection.Reifies * s_XqI r_Xph>
                 -> Sym
                      <(ReaderReflection.NTCo:Tag
                          <r_Xph> <s_XqI> <m_Xpj>)> <a_X4C>) ; Sym
                                                                 <(ReaderReflection.NTCo:ReaderT
                                                                     <r_Xph> <m_Xpj> <a_X4C>)>
          :: (forall r_Xph (m_Xpj :: * -> *).
              GHC.Base.Monad m_Xpj =>
              forall a_X4C.
              a_X4C
              -> forall s_XqI.
                 Data.Reflection.Reifies * s_XqI r_Xph =>
                 m_Xpj a_X4C)
               ~#
             (forall r_Xph (m_Xpj :: * -> *).
              GHC.Base.Monad m_Xpj =>
              forall a_X4C. a_X4C -> ReaderReflection.ReaderT r_Xph m_Xpj a_X4C))

ReaderReflection.$fMonadReaderT2
  :: forall r_Xpx (m_Xpz :: * -> *).
     GHC.Base.Monad m_Xpz =>
     forall a_t3y b_t3z.
     ReaderReflection.ReaderT r_Xpx m_Xpz a_t3y
     -> (a_t3y -> ReaderReflection.ReaderT r_Xpx m_Xpz b_t3z)
     -> forall s_apU.
        Data.Reflection.Reifies * s_apU r_Xpx =>
        m_Xpz b_t3z
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType U(SAAA)LLL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=4, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=False)
         Tmpl= \ (@ r_Xpx)
                 (@ (m_Xpz :: * -> *))
                 ($dMonad_XrV [Occ=Once] :: GHC.Base.Monad m_Xpz)
                 (@ a_t3y)
                 (@ b_t3z)
                 (m_ao8 [Occ=Once] :: ReaderReflection.ReaderT r_Xpx m_Xpz a_t3y)
                 (k_ao9 [Occ=OnceL!]
                    :: a_t3y -> ReaderReflection.ReaderT r_Xpx m_Xpz b_t3z)
                 (@ s_apU)
                 ($dReifies_apV :: Data.Reflection.Reifies * s_apU r_Xpx) ->
                 GHC.Base.>>=
                   @ m_Xpz
                   $dMonad_XrV
                   @ a_t3y
                   @ b_t3z
                   (((m_ao8
                      `cast` (<ReaderReflection.NTCo:ReaderT <r_Xpx> <m_Xpz> <a_t3y>>
                              :: ReaderReflection.ReaderT r_Xpx m_Xpz a_t3y
                                   ~#
                                 (forall s_any.
                                  Data.Reflection.Reifies * s_any r_Xpx =>
                                  ReaderReflection.Tag r_Xpx s_any m_Xpz a_t3y)))
                       @ s_apU $dReifies_apV)
                    `cast` (<ReaderReflection.NTCo:Tag <r_Xpx> <s_apU> <m_Xpz>> <a_t3y>
                            :: ReaderReflection.Tag r_Xpx s_apU m_Xpz a_t3y ~# m_Xpz a_t3y))
                   ((\ (x_at0 [Occ=Once] :: a_t3y) ->
                       ((k_ao9 x_at0)
                        `cast` (<ReaderReflection.NTCo:ReaderT <r_Xpx> <m_Xpz> <b_t3z>>
                                :: ReaderReflection.ReaderT r_Xpx m_Xpz b_t3z
                                     ~#
                                   (forall s_any.
                                    Data.Reflection.Reifies * s_any r_Xpx =>
                                    ReaderReflection.Tag r_Xpx s_any m_Xpz b_t3z)))
                         @ s_apU $dReifies_apV)
                    `cast` (<a_t3y>
                            -> <ReaderReflection.NTCo:Tag <r_Xpx> <s_apU> <m_Xpz>> <b_t3z>
                            :: (a_t3y -> ReaderReflection.Tag r_Xpx s_apU m_Xpz b_t3z)
                                 ~#
                               (a_t3y -> m_Xpz b_t3z)))}]
ReaderReflection.$fMonadReaderT2 =
  \ (@ r_Xpx)
    (@ (m_Xpz :: * -> *))
    ($dMonad_XrV :: GHC.Base.Monad m_Xpz)
    (@ a_t3y)
    (@ b_t3z)
    (m_ao8 :: ReaderReflection.ReaderT r_Xpx m_Xpz a_t3y)
    (k_ao9 :: a_t3y -> ReaderReflection.ReaderT r_Xpx m_Xpz b_t3z)
    (@ s_apU)
    ($dReifies_apV :: Data.Reflection.Reifies * s_apU r_Xpx) ->
    GHC.Base.>>=
      @ m_Xpz
      $dMonad_XrV
      @ a_t3y
      @ b_t3z
      (((m_ao8
         `cast` (<ReaderReflection.NTCo:ReaderT <r_Xpx> <m_Xpz> <a_t3y>>
                 :: ReaderReflection.ReaderT r_Xpx m_Xpz a_t3y
                      ~#
                    (forall s_any.
                     Data.Reflection.Reifies * s_any r_Xpx =>
                     ReaderReflection.Tag r_Xpx s_any m_Xpz a_t3y)))
          @ s_apU $dReifies_apV)
       `cast` (<ReaderReflection.NTCo:Tag <r_Xpx> <s_apU> <m_Xpz>> <a_t3y>
               :: ReaderReflection.Tag r_Xpx s_apU m_Xpz a_t3y ~# m_Xpz a_t3y))
      ((\ (x_at0 :: a_t3y) ->
          ((k_ao9 x_at0)
           `cast` (<ReaderReflection.NTCo:ReaderT <r_Xpx> <m_Xpz> <b_t3z>>
                   :: ReaderReflection.ReaderT r_Xpx m_Xpz b_t3z
                        ~#
                      (forall s_any.
                       Data.Reflection.Reifies * s_any r_Xpx =>
                       ReaderReflection.Tag r_Xpx s_any m_Xpz b_t3z)))
            @ s_apU $dReifies_apV)
       `cast` (<a_t3y>
               -> <ReaderReflection.NTCo:Tag <r_Xpx> <s_apU> <m_Xpz>> <b_t3z>
               :: (a_t3y -> ReaderReflection.Tag r_Xpx s_apU m_Xpz b_t3z)
                    ~#
                  (a_t3y -> m_Xpz b_t3z)))

ReaderReflection.$fMonadReaderT_$c>>=
  :: forall r_aon (m_aoo :: * -> *).
     GHC.Base.Monad m_aoo =>
     forall a_apW b_apX.
     ReaderReflection.ReaderT r_aon m_aoo a_apW
     -> (a_apW -> ReaderReflection.ReaderT r_aon m_aoo b_apX)
     -> ReaderReflection.ReaderT r_aon m_aoo b_apX
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType U(SAAA)LLL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= ReaderReflection.$fMonadReaderT2
               `cast` (forall r_XqD (m_XqG :: * -> *).
                       <GHC.Base.Monad m_XqG>
                       -> forall a_X4G b_X4I.
                          <ReaderReflection.ReaderT r_XqD m_XqG a_X4G>
                          -> <a_X4G -> ReaderReflection.ReaderT r_XqD m_XqG b_X4I>
                          -> (forall s_Xr4.
                              <Data.Reflection.Reifies * s_Xr4 r_XqD>
                              -> Sym
                                   <(ReaderReflection.NTCo:Tag
                                       <r_XqD> <s_Xr4> <m_XqG>)> <b_X4I>) ; Sym
                                                                              <(ReaderReflection.NTCo:ReaderT
                                                                                  <r_XqD>
                                                                                  <m_XqG>
                                                                                  <b_X4I>)>
                       :: (forall r_XqD (m_XqG :: * -> *).
                           GHC.Base.Monad m_XqG =>
                           forall a_X4G b_X4I.
                           ReaderReflection.ReaderT r_XqD m_XqG a_X4G
                           -> (a_X4G -> ReaderReflection.ReaderT r_XqD m_XqG b_X4I)
                           -> forall s_Xr4.
                              Data.Reflection.Reifies * s_Xr4 r_XqD =>
                              m_XqG b_X4I)
                            ~#
                          (forall r_XqD (m_XqG :: * -> *).
                           GHC.Base.Monad m_XqG =>
                           forall a_X4G b_X4I.
                           ReaderReflection.ReaderT r_XqD m_XqG a_X4G
                           -> (a_X4G -> ReaderReflection.ReaderT r_XqD m_XqG b_X4I)
                           -> ReaderReflection.ReaderT r_XqD m_XqG b_X4I))}]
ReaderReflection.$fMonadReaderT_$c>>= =
  ReaderReflection.$fMonadReaderT2
  `cast` (forall r_XqD (m_XqG :: * -> *).
          <GHC.Base.Monad m_XqG>
          -> forall a_X4G b_X4I.
             <ReaderReflection.ReaderT r_XqD m_XqG a_X4G>
             -> <a_X4G -> ReaderReflection.ReaderT r_XqD m_XqG b_X4I>
             -> (forall s_Xr4.
                 <Data.Reflection.Reifies * s_Xr4 r_XqD>
                 -> Sym
                      <(ReaderReflection.NTCo:Tag
                          <r_XqD> <s_Xr4> <m_XqG>)> <b_X4I>) ; Sym
                                                                 <(ReaderReflection.NTCo:ReaderT
                                                                     <r_XqD> <m_XqG> <b_X4I>)>
          :: (forall r_XqD (m_XqG :: * -> *).
              GHC.Base.Monad m_XqG =>
              forall a_X4G b_X4I.
              ReaderReflection.ReaderT r_XqD m_XqG a_X4G
              -> (a_X4G -> ReaderReflection.ReaderT r_XqD m_XqG b_X4I)
              -> forall s_Xr4.
                 Data.Reflection.Reifies * s_Xr4 r_XqD =>
                 m_XqG b_X4I)
               ~#
             (forall r_XqD (m_XqG :: * -> *).
              GHC.Base.Monad m_XqG =>
              forall a_X4G b_X4I.
              ReaderReflection.ReaderT r_XqD m_XqG a_X4G
              -> (a_X4G -> ReaderReflection.ReaderT r_XqD m_XqG b_X4I)
              -> ReaderReflection.ReaderT r_XqD m_XqG b_X4I))

ReaderReflection.$fMonadReaderT_$cfail
  :: forall r_aon (m_aoo :: * -> *).
     GHC.Base.Monad m_aoo =>
     forall a_ar7.
     GHC.Base.String -> ReaderReflection.ReaderT r_aon m_aoo a_ar7
[GblId,
 Arity=2,
 Str=DmdType ASb,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_XpG)
                 (@ (m_XpI :: * -> *))
                 _
                 (@ a_atc)
                 (eta_XY [Occ=Once] :: [GHC.Types.Char]) ->
                 GHC.Err.error
                   @ (ReaderReflection.ReaderT r_XpG m_XpI a_atc) eta_XY}]
ReaderReflection.$fMonadReaderT_$cfail =
  \ (@ r_XpG)
    (@ (m_XpI :: * -> *))
    _
    (@ a_atc)
    (eta_XY :: [GHC.Types.Char]) ->
    GHC.Err.error @ (ReaderReflection.ReaderT r_XpG m_XpI a_atc) eta_XY

a1_ruQ
  :: forall r_XpF (m_XpH :: * -> *).
     GHC.Base.Monad m_XpH =>
     forall a_XrQ b_XrS.
     ReaderReflection.ReaderT r_XpF m_XpH a_XrQ
     -> ReaderReflection.ReaderT r_XpF m_XpH b_XrS
     -> forall s_any.
        Data.Reflection.Reifies * s_any r_XpF =>
        m_XpH b_XrS
[GblId, Arity=4, Caf=NoCafRefs, Str=DmdType U(SAAA)LLL]
a1_ruQ =
  \ (@ r_XpF)
    (@ (m_XpH :: * -> *))
    ($dMonad_Xs3 :: GHC.Base.Monad m_XpH)
    (@ a_XrQ)
    (@ b_XrS)
    (eta_X11 :: ReaderReflection.ReaderT r_XpF m_XpH a_XrQ)
    (eta1_X21 :: ReaderReflection.ReaderT r_XpF m_XpH b_XrS)
    (@ s_any)
    (eta2_X3 :: Data.Reflection.Reifies * s_any r_XpF) ->
    let {
      lvl2_suF :: ReaderReflection.Tag r_XpF s_any m_XpH b_XrS
      [LclId]
      lvl2_suF =
        (eta1_X21
         `cast` (<ReaderReflection.NTCo:ReaderT <r_XpF> <m_XpH> <b_XrS>>
                 :: ReaderReflection.ReaderT r_XpF m_XpH b_XrS
                      ~#
                    (forall s_any.
                     Data.Reflection.Reifies * s_any r_XpF =>
                     ReaderReflection.Tag r_XpF s_any m_XpH b_XrS)))
          @ s_any eta2_X3 } in
    GHC.Base.>>=
      @ m_XpH
      $dMonad_Xs3
      @ a_XrQ
      @ b_XrS
      (((eta_X11
         `cast` (<ReaderReflection.NTCo:ReaderT <r_XpF> <m_XpH> <a_XrQ>>
                 :: ReaderReflection.ReaderT r_XpF m_XpH a_XrQ
                      ~#
                    (forall s_any.
                     Data.Reflection.Reifies * s_any r_XpF =>
                     ReaderReflection.Tag r_XpF s_any m_XpH a_XrQ)))
          @ s_any eta2_X3)
       `cast` (<ReaderReflection.NTCo:Tag <r_XpF> <s_any> <m_XpH>> <a_XrQ>
               :: ReaderReflection.Tag r_XpF s_any m_XpH a_XrQ ~# m_XpH a_XrQ))
      ((\ _ -> lvl2_suF)
       `cast` (<a_XrQ>
               -> <ReaderReflection.NTCo:Tag <r_XpF> <s_any> <m_XpH>> <b_XrS>
               :: (a_XrQ -> ReaderReflection.Tag r_XpF s_any m_XpH b_XrS)
                    ~#
                  (a_XrQ -> m_XpH b_XrS)))

ReaderReflection.$fMonadReaderT_$c>> [InlPrag=INLINE (sat-args=2)]
  :: forall r_aon (m_aoo :: * -> *).
     GHC.Base.Monad m_aoo =>
     forall a_aqT b_aqU.
     ReaderReflection.ReaderT r_aon m_aoo a_aqT
     -> ReaderReflection.ReaderT r_aon m_aoo b_aqU
     -> ReaderReflection.ReaderT r_aon m_aoo b_aqU
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType U(SAAA)LLL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=False,boring_ok=False)
         Tmpl= \ (@ r_XqA)
                 (@ (m_XqD :: * -> *))
                 ($dMonad_Xt0 [Occ=Once] :: GHC.Base.Monad m_XqD)
                 (@ a_at5)
                 (@ b_at6)
                 (m_at7 [Occ=Once] :: ReaderReflection.ReaderT r_XqA m_XqD a_at5)
                 (k_at8 [Occ=OnceL]
                    :: ReaderReflection.ReaderT r_XqA m_XqD b_at6) ->
                 ReaderReflection.$fMonadReaderT_$c>>=
                   @ r_XqA @ m_XqD $dMonad_Xt0 @ a_at5 @ b_at6 m_at7 (\ _ -> k_at8)}]
ReaderReflection.$fMonadReaderT_$c>> =
  a1_ruQ
  `cast` (forall r_XqK (m_XqN :: * -> *).
          <GHC.Base.Monad m_XqN>
          -> forall a_XsX b_Xt0.
             <ReaderReflection.ReaderT r_XqK m_XqN a_XsX>
             -> <ReaderReflection.ReaderT r_XqK m_XqN b_Xt0>
             -> (forall s_XoH.
                 <Data.Reflection.Reifies * s_XoH r_XqK>
                 -> Sym
                      <(ReaderReflection.NTCo:Tag
                          <r_XqK> <s_XoH> <m_XqN>)> <b_Xt0>) ; Sym
                                                                 <(ReaderReflection.NTCo:ReaderT
                                                                     <r_XqK> <m_XqN> <b_Xt0>)>
          :: (forall r_XqK (m_XqN :: * -> *).
              GHC.Base.Monad m_XqN =>
              forall a_XsX b_Xt0.
              ReaderReflection.ReaderT r_XqK m_XqN a_XsX
              -> ReaderReflection.ReaderT r_XqK m_XqN b_Xt0
              -> forall s_XoH.
                 Data.Reflection.Reifies * s_XoH r_XqK =>
                 m_XqN b_Xt0)
               ~#
             (forall r_XqK (m_XqN :: * -> *).
              GHC.Base.Monad m_XqN =>
              forall a_XsX b_Xt0.
              ReaderReflection.ReaderT r_XqK m_XqN a_XsX
              -> ReaderReflection.ReaderT r_XqK m_XqN b_Xt0
              -> ReaderReflection.ReaderT r_XqK m_XqN b_Xt0))

lvl1_ruR
  :: forall r_XpE (m_XpG :: * -> *) a_atc.
     [GHC.Types.Char] -> ReaderReflection.ReaderT r_XpE m_XpG a_atc
[GblId, Arity=1, Str=DmdType Tb]
lvl1_ruR =
  \ (@ r_XpE)
    (@ (m_XpG :: * -> *))
    (@ a_atc)
    (eta_X1b :: [GHC.Types.Char]) ->
    GHC.Err.error
      @ (ReaderReflection.ReaderT r_XpE m_XpG a_atc) eta_X1b

ReaderReflection.$fMonadReaderT [InlPrag=[ALWAYS] CONLIKE]
  :: forall r_aon (m_aoo :: * -> *).
     GHC.Base.Monad m_aoo =>
     GHC.Base.Monad (ReaderReflection.ReaderT r_aon m_aoo)
[GblId[DFunId],
 Arity=1,
 Str=DmdType Lm,
 Unf=DFun(arity=3) GHC.Base.D:Monad [{ReaderReflection.$fMonadReaderT_$c>>=},
                                     {ReaderReflection.$fMonadReaderT_$c>>},
                                     {ReaderReflection.$fMonadReaderT_$creturn},
                                     {ReaderReflection.$fMonadReaderT_$cfail}]]
ReaderReflection.$fMonadReaderT =
  \ (@ r_XpE)
    (@ (m_XpG :: * -> *))
    ($dMonad_Xs2 :: GHC.Base.Monad m_XpG) ->
    let {
      lvl2_suH :: forall a_X4U. a_X4U -> m_XpG a_X4U
      [LclId]
      lvl2_suH =
        \ (@ a_X4U) -> GHC.Base.return @ m_XpG $dMonad_Xs2 @ a_X4U } in
    GHC.Base.D:Monad
      @ (ReaderReflection.ReaderT r_XpE m_XpG)
      ((ReaderReflection.$fMonadReaderT2 @ r_XpE @ m_XpG $dMonad_Xs2)
       `cast` (forall a_X4G b_X4I.
               <ReaderReflection.ReaderT r_XpE m_XpG a_X4G>
               -> <a_X4G -> ReaderReflection.ReaderT r_XpE m_XpG b_X4I>
               -> (forall s_Xr4.
                   <Data.Reflection.Reifies * s_Xr4 r_XpE>
                   -> Sym
                        <(ReaderReflection.NTCo:Tag
                            <r_XpE> <s_Xr4> <m_XpG>)> <b_X4I>) ; Sym
                                                                   <(ReaderReflection.NTCo:ReaderT
                                                                       <r_XpE> <m_XpG> <b_X4I>)>
               :: (forall a_X4G b_X4I.
                   ReaderReflection.ReaderT r_XpE m_XpG a_X4G
                   -> (a_X4G -> ReaderReflection.ReaderT r_XpE m_XpG b_X4I)
                   -> forall s_Xr4.
                      Data.Reflection.Reifies * s_Xr4 r_XpE =>
                      m_XpG b_X4I)
                    ~#
                  (forall a_X4G b_X4I.
                   ReaderReflection.ReaderT r_XpE m_XpG a_X4G
                   -> (a_X4G -> ReaderReflection.ReaderT r_XpE m_XpG b_X4I)
                   -> ReaderReflection.ReaderT r_XpE m_XpG b_X4I)))
      (ReaderReflection.$fMonadReaderT_$c>> @ r_XpE @ m_XpG $dMonad_Xs2)
      ((\ (@ a_X4U) (a2_Xpq :: a_X4U) (@ s_Xr1) _ ->
          lvl2_suH @ a_X4U a2_Xpq)
       `cast` (forall a_X4C.
               <a_X4C>
               -> (forall s_XqI.
                   <Data.Reflection.Reifies * s_XqI r_XpE>
                   -> Sym
                        <(ReaderReflection.NTCo:Tag
                            <r_XpE> <s_XqI> <m_XpG>)> <a_X4C>) ; Sym
                                                                   <(ReaderReflection.NTCo:ReaderT
                                                                       <r_XpE> <m_XpG> <a_X4C>)>
               :: (forall a_X4C.
                   a_X4C
                   -> forall s_XqI.
                      Data.Reflection.Reifies * s_XqI r_XpE =>
                      m_XpG a_X4C)
                    ~#
                  (forall a_X4C.
                   a_X4C -> ReaderReflection.ReaderT r_XpE m_XpG a_X4C)))
      (lvl1_ruR @ r_XpE @ m_XpG)

ReaderReflection.$fMonadIOReaderT1
  :: forall r_aol (m_aom :: * -> *).
     (GHC.Base.Monad (ReaderReflection.ReaderT r_aol m_aom),
      Control.Monad.IO.Class.MonadIO m_aom) =>
     forall a_t3u.
     GHC.Types.IO a_t3u
     -> forall s_apg.
        Data.Reflection.Reifies * s_apg r_aol =>
        m_aom a_t3u
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType AU(AS)LA,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=4, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_aol)
                 (@ (m_aom :: * -> *))
                 _
                 ($dMonadIO_aqz [Occ=Once] :: Control.Monad.IO.Class.MonadIO m_aom)
                 (@ a_t3u)
                 (m_aoi [Occ=Once] :: GHC.Types.IO a_t3u)
                 (@ s_apg)
                 _ ->
                 Control.Monad.IO.Class.liftIO @ m_aom $dMonadIO_aqz @ a_t3u m_aoi}]
ReaderReflection.$fMonadIOReaderT1 =
  \ (@ r_aol)
    (@ (m_aom :: * -> *))
    _
    ($dMonadIO_aqz :: Control.Monad.IO.Class.MonadIO m_aom)
    (@ a_t3u)
    (m_aoi :: GHC.Types.IO a_t3u)
    (@ s_apg)
    _ ->
    Control.Monad.IO.Class.liftIO @ m_aom $dMonadIO_aqz @ a_t3u m_aoi

ReaderReflection.$fMonadIOReaderT_$cliftIO
  :: forall r_aol (m_aom :: * -> *).
     (GHC.Base.Monad (ReaderReflection.ReaderT r_aol m_aom),
      Control.Monad.IO.Class.MonadIO m_aom) =>
     forall a_api.
     GHC.Types.IO a_api -> ReaderReflection.ReaderT r_aol m_aom a_api
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType AU(AS)LA,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= ReaderReflection.$fMonadIOReaderT1
               `cast` (forall r_XqP (m_XpJ :: * -> *).
                       <GHC.Base.Monad (ReaderReflection.ReaderT r_XqP m_XpJ)>
                       -> <Control.Monad.IO.Class.MonadIO m_XpJ>
                       -> forall a_X4S.
                          <GHC.Types.IO a_X4S>
                          -> (forall s_XqF.
                              <Data.Reflection.Reifies * s_XqF r_XqP>
                              -> Sym
                                   <(ReaderReflection.NTCo:Tag
                                       <r_XqP> <s_XqF> <m_XpJ>)> <a_X4S>) ; Sym
                                                                              <(ReaderReflection.NTCo:ReaderT
                                                                                  <r_XqP>
                                                                                  <m_XpJ>
                                                                                  <a_X4S>)>
                       :: (forall r_XqP (m_XpJ :: * -> *).
                           (GHC.Base.Monad (ReaderReflection.ReaderT r_XqP m_XpJ),
                            Control.Monad.IO.Class.MonadIO m_XpJ) =>
                           forall a_X4S.
                           GHC.Types.IO a_X4S
                           -> forall s_XqF.
                              Data.Reflection.Reifies * s_XqF r_XqP =>
                              m_XpJ a_X4S)
                            ~#
                          (forall r_XqP (m_XpJ :: * -> *).
                           (GHC.Base.Monad (ReaderReflection.ReaderT r_XqP m_XpJ),
                            Control.Monad.IO.Class.MonadIO m_XpJ) =>
                           forall a_X4S.
                           GHC.Types.IO a_X4S
                           -> ReaderReflection.ReaderT r_XqP m_XpJ a_X4S))}]
ReaderReflection.$fMonadIOReaderT_$cliftIO =
  ReaderReflection.$fMonadIOReaderT1
  `cast` (forall r_XqP (m_XpJ :: * -> *).
          <GHC.Base.Monad (ReaderReflection.ReaderT r_XqP m_XpJ)>
          -> <Control.Monad.IO.Class.MonadIO m_XpJ>
          -> forall a_X4S.
             <GHC.Types.IO a_X4S>
             -> (forall s_XqF.
                 <Data.Reflection.Reifies * s_XqF r_XqP>
                 -> Sym
                      <(ReaderReflection.NTCo:Tag
                          <r_XqP> <s_XqF> <m_XpJ>)> <a_X4S>) ; Sym
                                                                 <(ReaderReflection.NTCo:ReaderT
                                                                     <r_XqP> <m_XpJ> <a_X4S>)>
          :: (forall r_XqP (m_XpJ :: * -> *).
              (GHC.Base.Monad (ReaderReflection.ReaderT r_XqP m_XpJ),
               Control.Monad.IO.Class.MonadIO m_XpJ) =>
              forall a_X4S.
              GHC.Types.IO a_X4S
              -> forall s_XqF.
                 Data.Reflection.Reifies * s_XqF r_XqP =>
                 m_XpJ a_X4S)
               ~#
             (forall r_XqP (m_XpJ :: * -> *).
              (GHC.Base.Monad (ReaderReflection.ReaderT r_XqP m_XpJ),
               Control.Monad.IO.Class.MonadIO m_XpJ) =>
              forall a_X4S.
              GHC.Types.IO a_X4S -> ReaderReflection.ReaderT r_XqP m_XpJ a_X4S))

ReaderReflection.$fMonadIOReaderT [InlPrag=[ALWAYS] CONLIKE]
  :: forall r_aol (m_aom :: * -> *).
     (GHC.Base.Monad (ReaderReflection.ReaderT r_aol m_aom),
      Control.Monad.IO.Class.MonadIO m_aom) =>
     Control.Monad.IO.Class.MonadIO
       (ReaderReflection.ReaderT r_aol m_aom)
[GblId[DFunId[1]],
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType LLm,
 Unf=DFun(arity=4) Control.Monad.IO.Class.D:MonadIO [<2>,
                                                     {ReaderReflection.$fMonadIOReaderT_$cliftIO}]]
ReaderReflection.$fMonadIOReaderT =
  \ (@ r_XpM)
    (@ (m_XpO :: * -> *))
    ($dMonad_Xs1
       :: GHC.Base.Monad (ReaderReflection.ReaderT r_XpM m_XpO))
    ($dMonadIO_Xt5 :: Control.Monad.IO.Class.MonadIO m_XpO) ->
    let {
      lvl2_suI :: forall a_X4W. GHC.Types.IO a_X4W -> m_XpO a_X4W
      [LclId]
      lvl2_suI =
        \ (@ a_X4W) ->
          Control.Monad.IO.Class.liftIO @ m_XpO $dMonadIO_Xt5 @ a_X4W } in
    Control.Monad.IO.Class.D:MonadIO
      @ (ReaderReflection.ReaderT r_XpM m_XpO)
      $dMonad_Xs1
      ((\ (@ a_X4W) (m_XpL :: GHC.Types.IO a_X4W) (@ s_XqK) _ ->
          lvl2_suI @ a_X4W m_XpL)
       `cast` (forall a_X4S.
               <GHC.Types.IO a_X4S>
               -> (forall s_XqF.
                   <Data.Reflection.Reifies * s_XqF r_XpM>
                   -> Sym
                        <(ReaderReflection.NTCo:Tag
                            <r_XpM> <s_XqF> <m_XpO>)> <a_X4S>) ; Sym
                                                                   <(ReaderReflection.NTCo:ReaderT
                                                                       <r_XpM> <m_XpO> <a_X4S>)>
               :: (forall a_X4S.
                   GHC.Types.IO a_X4S
                   -> forall s_XqF.
                      Data.Reflection.Reifies * s_XqF r_XpM =>
                      m_XpO a_X4S)
                    ~#
                  (forall a_X4S.
                   GHC.Types.IO a_X4S -> ReaderReflection.ReaderT r_XpM m_XpO a_X4S)))

ReaderReflection.$fMonadTransReaderT1
  :: forall r_aok (m_t3p :: * -> *) a_t3q.
     GHC.Base.Monad m_t3p =>
     m_t3p a_t3q
     -> forall s_XoN.
        Data.Reflection.Reifies * s_XoN r_aok =>
        m_t3p a_t3q
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType ASA,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_aok)
                 (@ (m_t3p :: * -> *))
                 (@ a_t3q)
                 _
                 (eta_X16 [Occ=Once] :: m_t3p a_t3q)
                 (@ s_XoN)
                 _ ->
                 eta_X16}]
ReaderReflection.$fMonadTransReaderT1 =
  \ (@ r_aok)
    (@ (m_t3p :: * -> *))
    (@ a_t3q)
    _
    (eta_X16 :: m_t3p a_t3q)
    (@ s_XoN)
    _ ->
    eta_X16

ReaderReflection.$fMonadTransReaderT_$clift
  :: forall r_aok (m_aqc :: * -> *) a_aqd.
     GHC.Base.Monad m_aqc =>
     m_aqc a_aqd -> ReaderReflection.ReaderT r_aok m_aqc a_aqd
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType ASA,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= ReaderReflection.$fMonadTransReaderT1
               `cast` (forall r_XpD (m_X4J :: * -> *) a_X4L.
                       <GHC.Base.Monad m_X4J>
                       -> <m_X4J a_X4L>
                       -> (forall s_Xq9.
                           <Data.Reflection.Reifies * s_Xq9 r_XpD>
                           -> Sym
                                <(ReaderReflection.NTCo:Tag
                                    <r_XpD> <s_Xq9> <m_X4J>)> <a_X4L>) ; Sym
                                                                           <(ReaderReflection.NTCo:ReaderT
                                                                               <r_XpD>
                                                                               <m_X4J>
                                                                               <a_X4L>)>
                       :: (forall r_XpD (m_X4J :: * -> *) a_X4L.
                           GHC.Base.Monad m_X4J =>
                           m_X4J a_X4L
                           -> forall s_Xq9.
                              Data.Reflection.Reifies * s_Xq9 r_XpD =>
                              m_X4J a_X4L)
                            ~#
                          (forall r_XpD (m_X4J :: * -> *) a_X4L.
                           GHC.Base.Monad m_X4J =>
                           m_X4J a_X4L -> ReaderReflection.ReaderT r_XpD m_X4J a_X4L))}]
ReaderReflection.$fMonadTransReaderT_$clift =
  ReaderReflection.$fMonadTransReaderT1
  `cast` (forall r_XpD (m_X4J :: * -> *) a_X4L.
          <GHC.Base.Monad m_X4J>
          -> <m_X4J a_X4L>
          -> (forall s_Xq9.
              <Data.Reflection.Reifies * s_Xq9 r_XpD>
              -> Sym
                   <(ReaderReflection.NTCo:Tag
                       <r_XpD> <s_Xq9> <m_X4J>)> <a_X4L>) ; Sym
                                                              <(ReaderReflection.NTCo:ReaderT
                                                                  <r_XpD> <m_X4J> <a_X4L>)>
          :: (forall r_XpD (m_X4J :: * -> *) a_X4L.
              GHC.Base.Monad m_X4J =>
              m_X4J a_X4L
              -> forall s_Xq9.
                 Data.Reflection.Reifies * s_Xq9 r_XpD =>
                 m_X4J a_X4L)
               ~#
             (forall r_XpD (m_X4J :: * -> *) a_X4L.
              GHC.Base.Monad m_X4J =>
              m_X4J a_X4L -> ReaderReflection.ReaderT r_XpD m_X4J a_X4L))

ReaderReflection.$fMonadTransReaderT [InlPrag=INLINE (sat-args=0)]
  :: forall r_aok.
     Control.Monad.Trans.Class.MonadTrans
       (ReaderReflection.ReaderT r_aok)
[GblId[DFunId(nt)],
 Str=DmdType,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=False,boring_ok=True)
         Tmpl= ReaderReflection.$fMonadTransReaderT_$clift
               `cast` (forall r_XqL.
                       Sym
                         <(Control.Monad.Trans.Class.NTCo:MonadTrans
                             <ReaderReflection.ReaderT r_XqL>)>
                       :: (forall r_XqL (m_aqc :: * -> *) a_aqd.
                           GHC.Base.Monad m_aqc =>
                           m_aqc a_aqd -> ReaderReflection.ReaderT r_XqL m_aqc a_aqd)
                            ~#
                          (forall r_XqL.
                           Control.Monad.Trans.Class.MonadTrans
                             (ReaderReflection.ReaderT r_XqL)))}]
ReaderReflection.$fMonadTransReaderT =
  ReaderReflection.$fMonadTransReaderT1
  `cast` (forall r_XpE.
          (forall (m_X4K :: * -> *) a_X4M.
           <GHC.Base.Monad m_X4K>
           -> <m_X4K a_X4M>
           -> (forall s_Xqa.
               <Data.Reflection.Reifies * s_Xqa r_XpE>
               -> Sym
                    <(ReaderReflection.NTCo:Tag
                        <r_XpE> <s_Xqa> <m_X4K>)> <a_X4M>) ; Sym
                                                               <(ReaderReflection.NTCo:ReaderT
                                                                   <r_XpE> <m_X4K> <a_X4M>)>) ; Sym
                                                                                                  <(Control.Monad.Trans.Class.NTCo:MonadTrans
                                                                                                      <ReaderReflection.ReaderT
                                                                                                         r_XpE>)>
          :: (forall r_XpE (m_X4K :: * -> *) a_X4M.
              GHC.Base.Monad m_X4K =>
              m_X4K a_X4M
              -> forall s_Xqa.
                 Data.Reflection.Reifies * s_Xqa r_XpE =>
                 m_X4K a_X4M)
               ~#
             (forall r_XpE.
              Control.Monad.Trans.Class.MonadTrans
                (ReaderReflection.ReaderT r_XpE)))

ReaderReflection.$wa
  :: forall r_t1A (m_t1B :: * -> *) a_t1C.
     (forall a1_apW b_apX.
      m_t1B a1_apW -> (a1_apW -> m_t1B b_apX) -> m_t1B b_apX)
     -> (forall a1_apu. a1_apu -> m_t1B a1_apu)
     -> (r_t1A -> m_t1B a_t1C)
     -> forall s_XoY.
        Data.Reflection.Reifies * s_XoY r_t1A =>
        m_t1B a_t1C
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType SLLL,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=4, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=IF_ARGS [60 60 60 0] 81 0}]
ReaderReflection.$wa =
  \ (@ r_t1A)
    (@ (m_t1B :: * -> *))
    (@ a_t1C)
    (ww_suc
       :: forall a1_apW b_apX.
          m_t1B a1_apW -> (a1_apW -> m_t1B b_apX) -> m_t1B b_apX)
    (ww1_sue :: forall a1_apu. a1_apu -> m_t1B a1_apu)
    (w_suh :: r_t1A -> m_t1B a_t1C)
    (@ s_XoY)
    (w1_sui :: Data.Reflection.Reifies * s_XoY r_t1A) ->
    ww_suc
      @ r_t1A
      @ a_t1C
      (ww1_sue
         @ r_t1A
         ((w1_sui
           `cast` (<Data.Reflection.NTCo:Reifies <*> <s_XoY> <r_t1A>>
                   :: Data.Reflection.Reifies * s_XoY r_t1A
                        ~#
                      (forall (proxy_apx :: * -> *). proxy_apx s_XoY -> r_t1A)))
            @ (Data.Proxy.Proxy *) (Data.Proxy.Proxy @ * @ s_XoY)))
      (\ (x_XuJ :: r_t1A) -> w_suh x_XuJ)

ReaderReflection.readerT1 [InlPrag=INLINE[0]]
  :: forall r_t1A (m_t1B :: * -> *) a_t1C.
     GHC.Base.Monad m_t1B =>
     (r_t1A -> m_t1B a_t1C)
     -> forall s_XoY.
        Data.Reflection.Reifies * s_XoY r_t1A =>
        m_t1B a_t1C
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType U(SALA)LL,
 Unf=Unf{Src=Worker=ReaderReflection.$wa, TopLvl=True, Arity=3,
         Value=True, ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=False)
         Tmpl= \ (@ r_t1A)
                 (@ (m_t1B :: * -> *))
                 (@ a_t1C)
                 (w_sua [Occ=Once!] :: GHC.Base.Monad m_t1B)
                 (w1_suh [Occ=Once] :: r_t1A -> m_t1B a_t1C)
                 (@ s_XoY)
                 (w2_sui [Occ=Once] :: Data.Reflection.Reifies * s_XoY r_t1A) ->
                 case w_sua
                 of _ { GHC.Base.D:Monad ww_suc [Occ=Once] _ ww2_sue [Occ=Once] _ ->
                 ReaderReflection.$wa
                   @ r_t1A @ m_t1B @ a_t1C ww_suc ww2_sue w1_suh @ s_XoY w2_sui
                 }}]
ReaderReflection.readerT1 =
  \ (@ r_t1A)
    (@ (m_t1B :: * -> *))
    (@ a_t1C)
    (w_sua :: GHC.Base.Monad m_t1B)
    (w1_suh :: r_t1A -> m_t1B a_t1C)
    (@ s_XoY)
    (w2_sui :: Data.Reflection.Reifies * s_XoY r_t1A) ->
    case w_sua
    of _ { GHC.Base.D:Monad ww_suc ww1_sud ww2_sue ww3_suf ->
    ReaderReflection.$wa
      @ r_t1A @ m_t1B @ a_t1C ww_suc ww2_sue w1_suh @ s_XoY w2_sui
    }

ReaderReflection.readerT
  :: forall r_anT (m_anU :: * -> *) a_anV.
     GHC.Base.Monad m_anU =>
     (r_anT -> m_anU a_anV)
     -> ReaderReflection.ReaderT r_anT m_anU a_anV
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType U(SALA)LL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= ReaderReflection.readerT1
               `cast` (forall r_t1A (m_t1B :: * -> *) a_t1C.
                       <GHC.Base.Monad m_t1B>
                       -> <r_t1A -> m_t1B a_t1C>
                       -> (forall s_XoY.
                           <Data.Reflection.Reifies * s_XoY r_t1A>
                           -> Sym
                                <(ReaderReflection.NTCo:Tag
                                    <r_t1A> <s_XoY> <m_t1B>)> <a_t1C>) ; Sym
                                                                           <(ReaderReflection.NTCo:ReaderT
                                                                               <r_t1A>
                                                                               <m_t1B>
                                                                               <a_t1C>)>
                       :: (forall r_t1A (m_t1B :: * -> *) a_t1C.
                           GHC.Base.Monad m_t1B =>
                           (r_t1A -> m_t1B a_t1C)
                           -> forall s_XoY.
                              Data.Reflection.Reifies * s_XoY r_t1A =>
                              m_t1B a_t1C)
                            ~#
                          (forall r_t1A (m_t1B :: * -> *) a_t1C.
                           GHC.Base.Monad m_t1B =>
                           (r_t1A -> m_t1B a_t1C)
                           -> ReaderReflection.ReaderT r_t1A m_t1B a_t1C))}]
ReaderReflection.readerT =
  ReaderReflection.readerT1
  `cast` (forall r_t1A (m_t1B :: * -> *) a_t1C.
          <GHC.Base.Monad m_t1B>
          -> <r_t1A -> m_t1B a_t1C>
          -> (forall s_XoY.
              <Data.Reflection.Reifies * s_XoY r_t1A>
              -> Sym
                   <(ReaderReflection.NTCo:Tag
                       <r_t1A> <s_XoY> <m_t1B>)> <a_t1C>) ; Sym
                                                              <(ReaderReflection.NTCo:ReaderT
                                                                  <r_t1A> <m_t1B> <a_t1C>)>
          :: (forall r_t1A (m_t1B :: * -> *) a_t1C.
              GHC.Base.Monad m_t1B =>
              (r_t1A -> m_t1B a_t1C)
              -> forall s_XoY.
                 Data.Reflection.Reifies * s_XoY r_t1A =>
                 m_t1B a_t1C)
               ~#
             (forall r_t1A (m_t1B :: * -> *) a_t1C.
              GHC.Base.Monad m_t1B =>
              (r_t1A -> m_t1B a_t1C)
              -> ReaderReflection.ReaderT r_t1A m_t1B a_t1C))



[2 of 3] Compiling Eval1            ( Eval1.hs, build/Eval1.o )

==================== Tidy Core ====================
Result size of Tidy Core = {terms: 66, types: 147, coercions: 212}

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
         Guidance=IF_ARGS [0 0] 111 0}]
Eval1.runEval1 =
  \ (@ void_l)
    (m_aJ7 :: Eval1.Eval void_l)
    (eta_B1 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    case GHC.Prim.newMutVar#
           @ GHC.Types.Int @ GHC.Prim.RealWorld Eval1.runEval2 eta_B1
    of _ { (# ipv_aKO, ipv1_aKP #) ->
    let {
      a_sLc :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
      [LclId, Str=DmdType m]
      a_sLc =
        GHC.STRef.STRef @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_aKP } in
    case ((((\ (@ s_aqo)
               ($dReifies_aqp :: Data.Reflection.Reifies * s_aqo Eval1.Value)
               _ ->
               ((((\ (@ s1_XqU)
                     ($dReifies1_XqW :: Data.Reflection.Reifies * s1_XqU Eval1.Value)
                     _ ->
                     (m_aJ7
                      `cast` (<ReaderReflection.NTCo:ReaderT
                                 <Eval1.Value>
                                 <ReaderReflection.ReaderT Eval1.Value GHC.Types.IO>
                                 <void_l>>
                              :: ReaderReflection.ReaderT
                                   Eval1.Value
                                   (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                                   void_l
                                   ~#
                                 (forall s_any.
                                  Data.Reflection.Reifies * s_any Eval1.Value =>
                                  ReaderReflection.Tag
                                    Eval1.Value
                                    s_any
                                    (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                                    void_l)))
                       @ s1_XqU $dReifies1_XqW)
                  `cast` ((forall s1_XqU.
                           <Data.Reflection.Reifies * s1_XqU Eval1.Value>
                           -> <Data.Proxy.Proxy * s1_XqU>
                           -> <ReaderReflection.NTCo:Tag
                                 <Eval1.Value>
                                 <s1_XqU>
                                 <ReaderReflection.ReaderT
                                    Eval1.Value GHC.Types.IO>> <void_l>) ; (Sym
                                                                              <(Data.Reflection.NTCo:Magic
                                                                                  <Eval1.Value>
                                                                                  <ReaderReflection.ReaderT
                                                                                     Eval1.Value
                                                                                     GHC.Types.IO
                                                                                     void_l>)> ; UnsafeCo
                                                                                                   (Data.Reflection.Magic
                                                                                                      Eval1.Value
                                                                                                      (ReaderReflection.ReaderT
                                                                                                         Eval1.Value
                                                                                                         GHC.Types.IO
                                                                                                         void_l))
                                                                                                   ((GHC.Prim.Any
                                                                                                       *
                                                                                                     -> Eval1.Value)
                                                                                                    -> Data.Proxy.Proxy
                                                                                                         AnyK
                                                                                                         (GHC.Prim.Any
                                                                                                            AnyK)
                                                                                                    -> ReaderReflection.ReaderT
                                                                                                         Eval1.Value
                                                                                                         GHC.Types.IO
                                                                                                         void_l))
                          :: (forall s1_XqU.
                              Data.Reflection.Reifies * s1_XqU Eval1.Value =>
                              Data.Proxy.Proxy * s1_XqU
                              -> ReaderReflection.Tag
                                   Eval1.Value
                                   s1_XqU
                                   (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                                   void_l)
                               ~#
                             ((GHC.Prim.Any * -> Eval1.Value)
                              -> Data.Proxy.Proxy AnyK (GHC.Prim.Any AnyK)
                              -> ReaderReflection.ReaderT Eval1.Value GHC.Types.IO void_l)))
                   ((\ _ -> a_sLc)
                    `cast` (<GHC.Prim.Any *>
                            -> Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int>
                            :: (GHC.Prim.Any *
                                -> GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int)
                                 ~#
                               (GHC.Prim.Any * -> GHC.IORef.IORef GHC.Types.Int)))
                   (Data.Proxy.Proxy @ AnyK @ (GHC.Prim.Any AnyK)))
                `cast` (<ReaderReflection.NTCo:ReaderT
                           <Eval1.Value> <GHC.Types.IO> <void_l>>
                        :: ReaderReflection.ReaderT Eval1.Value GHC.Types.IO void_l
                             ~#
                           (forall s_any.
                            Data.Reflection.Reifies * s_any Eval1.Value =>
                            ReaderReflection.Tag Eval1.Value s_any GHC.Types.IO void_l)))
                 @ s_aqo $dReifies_aqp)
            `cast` ((forall s_aqo.
                     <Data.Reflection.Reifies * s_aqo Eval1.Value>
                     -> <Data.Proxy.Proxy * s_aqo>
                     -> <ReaderReflection.NTCo:Tag
                           <Eval1.Value> <s_aqo> <GHC.Types.IO>> <void_l>) ; (Sym
                                                                                <(Data.Reflection.NTCo:Magic
                                                                                    <Eval1.Value>
                                                                                    <GHC.Types.IO
                                                                                       void_l>)> ; UnsafeCo
                                                                                                     (Data.Reflection.Magic
                                                                                                        Eval1.Value
                                                                                                        (GHC.Types.IO
                                                                                                           void_l))
                                                                                                     ((GHC.Prim.Any
                                                                                                         *
                                                                                                       -> Eval1.Value)
                                                                                                      -> Data.Proxy.Proxy
                                                                                                           AnyK
                                                                                                           (GHC.Prim.Any
                                                                                                              AnyK)
                                                                                                      -> GHC.Types.IO
                                                                                                           void_l))
                    :: (forall s_aqo.
                        Data.Reflection.Reifies * s_aqo Eval1.Value =>
                        Data.Proxy.Proxy * s_aqo
                        -> ReaderReflection.Tag Eval1.Value s_aqo GHC.Types.IO void_l)
                         ~#
                       ((GHC.Prim.Any * -> Eval1.Value)
                        -> Data.Proxy.Proxy AnyK (GHC.Prim.Any AnyK)
                        -> GHC.Types.IO void_l)))
             ((\ _ -> a_sLc)
              `cast` (<GHC.Prim.Any *>
                      -> Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int>
                      :: (GHC.Prim.Any *
                          -> GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int)
                           ~#
                         (GHC.Prim.Any * -> GHC.IORef.IORef GHC.Types.Int)))
             (Data.Proxy.Proxy @ AnyK @ (GHC.Prim.Any AnyK)))
          `cast` (<GHC.Types.NTCo:IO <void_l>>
                  :: GHC.Types.IO void_l
                       ~#
                     (GHC.Prim.State# GHC.Prim.RealWorld
                      -> (# GHC.Prim.State# GHC.Prim.RealWorld, void_l #))))
           ipv_aKO
    of _ { (# ipv2_XLD, _ #) ->
    GHC.Prim.readMutVar#
      @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_aKP ipv2_XLD
    }
    }

Eval1.runEval
  :: forall void_aJ6.
     Eval1.Eval void_aJ6 -> GHC.Types.IO GHC.Types.Int
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
  :: forall s_apC.
     Data.Reflection.Reifies * s_apC Eval1.Value =>
     ReaderReflection.ReaderT
       (GHC.IORef.IORef GHC.Types.Int) GHC.Types.IO Eval1.Value
[GblId,
 Arity=1,
 Caf=NoCafRefs,
 Str=DmdType L,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=1, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=IF_ARGS [0] 31 60}]
Eval1.ask3 =
  \ (@ s_apC)
    ($dReifies_apD :: Data.Reflection.Reifies * s_apC Eval1.Value) ->
    let {
      a2_aob [Dmd=Just L] :: Eval1.Value
      [LclId, Str=DmdType]
      a2_aob =
        ($dReifies_apD
         `cast` (<Data.Reflection.NTCo:Reifies <*> <s_apC> <Eval1.Value>>
                 :: Data.Reflection.Reifies * s_apC Eval1.Value
                      ~#
                    (forall (proxy_apx :: * -> *). proxy_apx s_apC -> Eval1.Value)))
          @ (Data.Proxy.Proxy *) (Data.Proxy.Proxy @ * @ s_apC) } in
    (\ (@ s1_apL) _ (s_aLt :: GHC.Prim.State# GHC.Prim.RealWorld) ->
       (# s_aLt, a2_aob #))
    `cast` ((forall s1_apL.
             <Data.Reflection.Reifies * s1_apL (GHC.IORef.IORef GHC.Types.Int)>
             -> Sym <(GHC.Types.NTCo:IO <Eval1.Value>)> ; Sym
                                                            <(ReaderReflection.NTCo:Tag
                                                                <GHC.IORef.IORef GHC.Types.Int>
                                                                <s1_apL>
                                                                <GHC.Types.IO>)> <Eval1.Value>) ; Sym
                                                                                                    <(ReaderReflection.NTCo:ReaderT
                                                                                                        <GHC.IORef.IORef
                                                                                                           GHC.Types.Int>
                                                                                                        <GHC.Types.IO>
                                                                                                        <Eval1.Value>)>
            :: (forall s1_apL.
                Data.Reflection.Reifies * s1_apL (GHC.IORef.IORef GHC.Types.Int) =>
                GHC.Prim.State# GHC.Prim.RealWorld
                -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval1.Value #))
                 ~#
               ReaderReflection.ReaderT
                 (GHC.IORef.IORef GHC.Types.Int) GHC.Types.IO Eval1.Value)

Eval1.ask1 :: Eval1.Eval Eval1.Value
[GblId,
 Arity=1,
 Caf=NoCafRefs,
 Str=DmdType L,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval1.ask1 =
  Eval1.ask3
  `cast` ((forall s_apC.
           <Data.Reflection.Reifies * s_apC Eval1.Value>
           -> Sym
                <(ReaderReflection.NTCo:Tag
                    <Eval1.Value>
                    <s_apC>
                    <ReaderReflection.ReaderT
                       Eval1.Value GHC.Types.IO>)> <Eval1.Value>) ; Sym
                                                                      <(ReaderReflection.NTCo:ReaderT
                                                                          <Eval1.Value>
                                                                          <ReaderReflection.ReaderT
                                                                             Eval1.Value
                                                                             GHC.Types.IO>
                                                                          <Eval1.Value>)>
          :: (forall s_apC.
              Data.Reflection.Reifies * s_apC Eval1.Value =>
              ReaderReflection.ReaderT Eval1.Value GHC.Types.IO Eval1.Value)
               ~#
             ReaderReflection.ReaderT
               Eval1.Value
               (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
               Eval1.Value)

Eval1.ask4
  :: forall s_XoN.
     Data.Reflection.Reifies * s_XoN (GHC.IORef.IORef GHC.Types.Int) =>
     forall s1_XpZ.
     Data.Reflection.Reifies * s1_XpZ Eval1.Value =>
     GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval1.Value #)
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType ALL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=False)
         Tmpl= \ (@ s_XoN)
                 _
                 (@ s1_XpZ)
                 (eta_B2 [Occ=Once] :: Data.Reflection.Reifies * s1_XpZ Eval1.Value)
                 (eta2_B1 [Occ=Once] :: GHC.Prim.State# GHC.Prim.RealWorld) ->
                 (# eta2_B1,
                    (eta_B2
                     `cast` (<Data.Reflection.NTCo:Reifies <*> <s1_XpZ> <Eval1.Value>>
                             :: Data.Reflection.Reifies * s1_XpZ Eval1.Value
                                  ~#
                                (forall (proxy_apx :: * -> *). proxy_apx s1_XpZ -> Eval1.Value)))
                      @ (Data.Proxy.Proxy *) (Data.Proxy.Proxy @ * @ s1_XpZ) #)}]
Eval1.ask4 =
  \ (@ s_XoN)
    _
    (@ s1_XpZ)
    (eta_B2 :: Data.Reflection.Reifies * s1_XpZ Eval1.Value)
    (eta2_B1 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# eta2_B1,
       (eta_B2
        `cast` (<Data.Reflection.NTCo:Reifies <*> <s1_XpZ> <Eval1.Value>>
                :: Data.Reflection.Reifies * s1_XpZ Eval1.Value
                     ~#
                   (forall (proxy_apx :: * -> *). proxy_apx s1_XpZ -> Eval1.Value)))
         @ (Data.Proxy.Proxy *) (Data.Proxy.Proxy @ * @ s1_XpZ) #)

Eval1.ask2 :: Eval1.Eval Eval1.Value
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType ALL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Eval1.ask4
               `cast` ((forall s_XoN.
                        <Data.Reflection.Reifies * s_XoN (GHC.IORef.IORef GHC.Types.Int)>
                        -> (forall s1_Xqr.
                            <Data.Reflection.Reifies * s1_Xqr Eval1.Value>
                            -> Sym <(GHC.Types.NTCo:IO <Eval1.Value>)> ; Sym
                                                                           <(ReaderReflection.NTCo:Tag
                                                                               <Eval1.Value>
                                                                               <s1_Xqr>
                                                                               <GHC.Types.IO>)> <Eval1.Value>) ; (Sym
                                                                                                                    <(ReaderReflection.NTCo:ReaderT
                                                                                                                        <Eval1.Value>
                                                                                                                        <GHC.Types.IO>
                                                                                                                        <Eval1.Value>)> ; Sym
                                                                                                                                            <(ReaderReflection.NTCo:Tag
                                                                                                                                                <GHC.IORef.IORef
                                                                                                                                                   GHC.Types.Int>
                                                                                                                                                <s_XoN>
                                                                                                                                                <ReaderReflection.ReaderT
                                                                                                                                                   Eval1.Value
                                                                                                                                                   GHC.Types.IO>)> <Eval1.Value>)) ; Sym
                                                                                                                                                                                       <(ReaderReflection.NTCo:ReaderT
                                                                                                                                                                                           <GHC.IORef.IORef
                                                                                                                                                                                              GHC.Types.Int>
                                                                                                                                                                                           <ReaderReflection.ReaderT
                                                                                                                                                                                              Eval1.Value
                                                                                                                                                                                              GHC.Types.IO>
                                                                                                                                                                                           <Eval1.Value>)>
                       :: (forall s_XoN.
                           Data.Reflection.Reifies * s_XoN (GHC.IORef.IORef GHC.Types.Int) =>
                           forall s1_Xqr.
                           Data.Reflection.Reifies * s1_Xqr Eval1.Value =>
                           GHC.Prim.State# GHC.Prim.RealWorld
                           -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval1.Value #))
                            ~#
                          ReaderReflection.ReaderT
                            (GHC.IORef.IORef GHC.Types.Int)
                            (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                            Eval1.Value)}]
Eval1.ask2 =
  Eval1.ask4
  `cast` ((forall s_XoN.
           <Data.Reflection.Reifies * s_XoN (GHC.IORef.IORef GHC.Types.Int)>
           -> (forall s1_Xqr.
               <Data.Reflection.Reifies * s1_Xqr Eval1.Value>
               -> Sym <(GHC.Types.NTCo:IO <Eval1.Value>)> ; Sym
                                                              <(ReaderReflection.NTCo:Tag
                                                                  <Eval1.Value>
                                                                  <s1_Xqr>
                                                                  <GHC.Types.IO>)> <Eval1.Value>) ; (Sym
                                                                                                       <(ReaderReflection.NTCo:ReaderT
                                                                                                           <Eval1.Value>
                                                                                                           <GHC.Types.IO>
                                                                                                           <Eval1.Value>)> ; Sym
                                                                                                                               <(ReaderReflection.NTCo:Tag
                                                                                                                                   <GHC.IORef.IORef
                                                                                                                                      GHC.Types.Int>
                                                                                                                                   <s_XoN>
                                                                                                                                   <ReaderReflection.ReaderT
                                                                                                                                      Eval1.Value
                                                                                                                                      GHC.Types.IO>)> <Eval1.Value>)) ; Sym
                                                                                                                                                                          <(ReaderReflection.NTCo:ReaderT
                                                                                                                                                                              <GHC.IORef.IORef
                                                                                                                                                                                 GHC.Types.Int>
                                                                                                                                                                              <ReaderReflection.ReaderT
                                                                                                                                                                                 Eval1.Value
                                                                                                                                                                                 GHC.Types.IO>
                                                                                                                                                                              <Eval1.Value>)>
          :: (forall s_XoN.
              Data.Reflection.Reifies * s_XoN (GHC.IORef.IORef GHC.Types.Int) =>
              forall s1_Xqr.
              Data.Reflection.Reifies * s1_Xqr Eval1.Value =>
              GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval1.Value #))
               ~#
             ReaderReflection.ReaderT
               (GHC.IORef.IORef GHC.Types.Int)
               (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
               Eval1.Value)



[3 of 3] Compiling OptimizeMonadTrans ( OptimizeMonadTrans.hs, build/OptimizeMonadTrans.o )

==================== Tidy Core ====================
Result size of Tidy Core = {terms: 176, types: 312, coercions: 352}

a_r1iG :: GHC.Types.Int
[GblId, Caf=NoCafRefs, Str=DmdType m]
a_r1iG = GHC.Types.I# 1

a1_r1iH
  :: forall s_Xqs.
     Data.Reflection.Reifies * s_Xqs (GHC.IORef.IORef GHC.Types.Int) =>
     forall s1_Xqw.
     Data.Reflection.Reifies * s1_Xqw (GHC.IORef.IORef GHC.Types.Int) =>
     GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #)
[GblId, Arity=3, Caf=NoCafRefs, Str=DmdType AAL]
a1_r1iH =
  \ (@ s_Xqs)
    _
    (@ s1_Xqw)
    _
    (s_aLt :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# s_aLt, a_r1iG #)

a2_r1iI :: GHC.Types.Int
[GblId, Caf=NoCafRefs, Str=DmdType m]
a2_r1iI = GHC.Types.I# 2

a3_r1iJ
  :: forall s_XqC.
     Data.Reflection.Reifies * s_XqC (GHC.IORef.IORef GHC.Types.Int) =>
     forall s1_XqG.
     Data.Reflection.Reifies * s1_XqG (GHC.IORef.IORef GHC.Types.Int) =>
     GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #)
[GblId, Arity=3, Caf=NoCafRefs, Str=DmdType AAL]
a3_r1iJ =
  \ (@ s_XqC)
    _
    (@ s1_XqG)
    _
    (s_aLt :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# s_aLt, a2_r1iI #)

a4_r1iK :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a4_r1iK =
  GHC.Types.:
    @ OptimizeMonadTrans.Tree
    OptimizeMonadTrans.Leaf
    (GHC.Types.[] @ OptimizeMonadTrans.Tree)

a5_r1iL :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a5_r1iL =
  GHC.Types.:
    @ OptimizeMonadTrans.Tree OptimizeMonadTrans.Leaf a4_r1iK

a6_r1iM :: OptimizeMonadTrans.Tree
[GblId, Caf=NoCafRefs, Str=DmdType]
a6_r1iM =
  OptimizeMonadTrans.Branch
    (a3_r1iJ
     `cast` ((forall s_Xr5.
              <Data.Reflection.Reifies * s_Xr5 (GHC.IORef.IORef GHC.Types.Int)>
              -> (forall s1_Xra.
                  <Data.Reflection.Reifies * s1_Xra (GHC.IORef.IORef GHC.Types.Int)>
                  -> Sym <(GHC.Types.NTCo:IO <GHC.Types.Int>)> ; Sym
                                                                   <(ReaderReflection.NTCo:Tag
                                                                       <GHC.IORef.IORef
                                                                          GHC.Types.Int>
                                                                       <s1_Xra>
                                                                       <GHC.Types.IO>)> <GHC.Types.Int>) ; (Sym
                                                                                                              <(ReaderReflection.NTCo:ReaderT
                                                                                                                  <GHC.IORef.IORef
                                                                                                                     GHC.Types.Int>
                                                                                                                  <GHC.Types.IO>
                                                                                                                  <GHC.Types.Int>)> ; Sym
                                                                                                                                        <(ReaderReflection.NTCo:Tag
                                                                                                                                            <GHC.IORef.IORef
                                                                                                                                               GHC.Types.Int>
                                                                                                                                            <s_Xr5>
                                                                                                                                            <ReaderReflection.ReaderT
                                                                                                                                               Eval1.Value
                                                                                                                                               GHC.Types.IO>)> <GHC.Types.Int>)) ; Sym
                                                                                                                                                                                     <(ReaderReflection.NTCo:ReaderT
                                                                                                                                                                                         <GHC.IORef.IORef
                                                                                                                                                                                            GHC.Types.Int>
                                                                                                                                                                                         <ReaderReflection.ReaderT
                                                                                                                                                                                            Eval1.Value
                                                                                                                                                                                            GHC.Types.IO>
                                                                                                                                                                                         <GHC.Types.Int>)>
             :: (forall s_Xr5.
                 Data.Reflection.Reifies * s_Xr5 (GHC.IORef.IORef GHC.Types.Int) =>
                 forall s1_Xra.
                 Data.Reflection.Reifies * s1_Xra (GHC.IORef.IORef GHC.Types.Int) =>
                 GHC.Prim.State# GHC.Prim.RealWorld
                 -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #))
                  ~#
                ReaderReflection.ReaderT
                  (GHC.IORef.IORef GHC.Types.Int)
                  (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                  GHC.Types.Int))
    a5_r1iL

a7_r1iN :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a7_r1iN = GHC.Types.: @ OptimizeMonadTrans.Tree a6_r1iM a4_r1iK

tree_rPN :: OptimizeMonadTrans.Tree
[GblId, Caf=NoCafRefs, Str=DmdType]
tree_rPN =
  OptimizeMonadTrans.Branch
    (a1_r1iH
     `cast` ((forall s_Xre.
              <Data.Reflection.Reifies * s_Xre (GHC.IORef.IORef GHC.Types.Int)>
              -> (forall s1_Xqw.
                  <Data.Reflection.Reifies * s1_Xqw (GHC.IORef.IORef GHC.Types.Int)>
                  -> Sym <(GHC.Types.NTCo:IO <GHC.Types.Int>)> ; Sym
                                                                   <(ReaderReflection.NTCo:Tag
                                                                       <GHC.IORef.IORef
                                                                          GHC.Types.Int>
                                                                       <s1_Xqw>
                                                                       <GHC.Types.IO>)> <GHC.Types.Int>) ; (Sym
                                                                                                              <(ReaderReflection.NTCo:ReaderT
                                                                                                                  <GHC.IORef.IORef
                                                                                                                     GHC.Types.Int>
                                                                                                                  <GHC.Types.IO>
                                                                                                                  <GHC.Types.Int>)> ; Sym
                                                                                                                                        <(ReaderReflection.NTCo:Tag
                                                                                                                                            <GHC.IORef.IORef
                                                                                                                                               GHC.Types.Int>
                                                                                                                                            <s_Xre>
                                                                                                                                            <ReaderReflection.ReaderT
                                                                                                                                               Eval1.Value
                                                                                                                                               GHC.Types.IO>)> <GHC.Types.Int>)) ; Sym
                                                                                                                                                                                     <(ReaderReflection.NTCo:ReaderT
                                                                                                                                                                                         <GHC.IORef.IORef
                                                                                                                                                                                            GHC.Types.Int>
                                                                                                                                                                                         <ReaderReflection.ReaderT
                                                                                                                                                                                            Eval1.Value
                                                                                                                                                                                            GHC.Types.IO>
                                                                                                                                                                                         <GHC.Types.Int>)>
             :: (forall s_Xre.
                 Data.Reflection.Reifies * s_Xre (GHC.IORef.IORef GHC.Types.Int) =>
                 forall s1_Xqw.
                 Data.Reflection.Reifies * s1_Xqw (GHC.IORef.IORef GHC.Types.Int) =>
                 GHC.Prim.State# GHC.Prim.RealWorld
                 -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #))
                  ~#
                ReaderReflection.ReaderT
                  (GHC.IORef.IORef GHC.Types.Int)
                  (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                  GHC.Types.Int))
    a7_r1iN

lvl_r1iO
  :: forall s_Xo3.
     Data.Reflection.Reifies * s_Xo3 (GHC.IORef.IORef GHC.Types.Int) =>
     GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld,
           [OptimizeMonadTrans.Tree] #)
[GblId, Arity=2, Caf=NoCafRefs]
lvl_r1iO =
  \ (@ s_Xo3)
    (eta_B2
       :: Data.Reflection.Reifies * s_Xo3 (GHC.IORef.IORef GHC.Types.Int))
    (eta1_Xy :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    case ((eta_B2
           `cast` (<Data.Reflection.NTCo:Reifies <*> <s_Xo3> <Eval1.Value>>
                   :: Data.Reflection.Reifies * s_Xo3 Eval1.Value
                        ~#
                      (forall (proxy_apx :: * -> *). proxy_apx s_Xo3 -> Eval1.Value)))
            @ (Data.Proxy.Proxy *) (Data.Proxy.Proxy @ * @ s_Xo3))
         `cast` (<GHC.IORef.NTCo:IORef> <GHC.Types.Int>
                 :: GHC.IORef.IORef GHC.Types.Int
                      ~#
                    GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int)
    of _ { GHC.STRef.STRef var#_aLj ->
    case GHC.Prim.readMutVar#
           @ GHC.Prim.RealWorld @ GHC.Types.Int var#_aLj eta1_Xy
    of _ { (# ipv_aL7, ipv1_aL8 #) ->
    case ipv1_aL8 of _ { GHC.Types.I# x_a10D ->
    case GHC.Prim.writeMutVar#
           @ GHC.Prim.RealWorld
           @ GHC.Types.Int
           var#_aLj
           (GHC.Types.I# (GHC.Prim.+# x_a10D 1))
           ipv_aL7
    of s2#_a12g { __DEFAULT ->
    (# s2#_a12g, GHC.Types.[] @ OptimizeMonadTrans.Tree #)
    }
    }
    }
    }

lvl1_r1iP
  :: forall s_Xrd.
     Data.Reflection.Reifies * s_Xrd (GHC.IORef.IORef GHC.Types.Int) =>
     GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #)
[GblId, Arity=2, Caf=NoCafRefs]
lvl1_r1iP =
  \ (@ s_Xrd) _ (s_XM8 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# s_XM8, GHC.Tuple.() #)

Rec {
a8_r1iQ
  :: [OptimizeMonadTrans.Tree]
     -> forall s_any.
        Data.Reflection.Reifies * s_any Eval1.Value =>
        ReaderReflection.Tag
          Eval1.Value
          s_any
          (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
          ()
[GblId, Arity=2, Caf=NoCafRefs, Str=DmdType SL]
a8_r1iQ =
  \ (ds_dZ6 :: [OptimizeMonadTrans.Tree])
    (@ s_any)
    (eta_B1 :: Data.Reflection.Reifies * s_any Eval1.Value) ->
    case ds_dZ6 of _ {
      [] ->
        lvl1_r1iP
        `cast` ((forall s1_Xrd.
                 <Data.Reflection.Reifies * s1_Xrd (GHC.IORef.IORef GHC.Types.Int)>
                 -> Sym <(GHC.Types.NTCo:IO <()>)> ; Sym
                                                       <(ReaderReflection.NTCo:Tag
                                                           <GHC.IORef.IORef GHC.Types.Int>
                                                           <s1_Xrd>
                                                           <GHC.Types.IO>)> <()>) ; (Sym
                                                                                       <(ReaderReflection.NTCo:ReaderT
                                                                                           <GHC.IORef.IORef
                                                                                              GHC.Types.Int>
                                                                                           <GHC.Types.IO>
                                                                                           <()>)> ; Sym
                                                                                                      <(ReaderReflection.NTCo:Tag
                                                                                                          <GHC.IORef.IORef
                                                                                                             GHC.Types.Int>
                                                                                                          <s_any>
                                                                                                          <ReaderReflection.ReaderT
                                                                                                             Eval1.Value
                                                                                                             GHC.Types.IO>)> <()>)
                :: (forall s1_Xrd.
                    Data.Reflection.Reifies * s1_Xrd (GHC.IORef.IORef GHC.Types.Int) =>
                    GHC.Prim.State# GHC.Prim.RealWorld
                    -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #))
                     ~#
                   ReaderReflection.Tag
                     (GHC.IORef.IORef GHC.Types.Int)
                     s_any
                     (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                     ());
      : x_aTj xs_aTk ->
        let {
          a11_s13y [Dmd=Just L]
            :: ReaderReflection.Tag
                 (GHC.IORef.IORef GHC.Types.Int)
                 s_any
                 (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                 [OptimizeMonadTrans.Tree]
          [LclId, Str=DmdType]
          a11_s13y =
            case x_aTj of _ {
              OptimizeMonadTrans.Branch action_aTm children_aTn ->
                let {
                  a12_s13s [Dmd=Just L]
                    :: ReaderReflection.Tag
                         (GHC.IORef.IORef GHC.Types.Int)
                         s_any
                         (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                         GHC.Types.Int
                  [LclId, Str=DmdType]
                  a12_s13s =
                    (action_aTm
                     `cast` (<ReaderReflection.NTCo:ReaderT
                                <GHC.IORef.IORef GHC.Types.Int>
                                <ReaderReflection.ReaderT Eval1.Value GHC.Types.IO>
                                <GHC.Types.Int>>
                             :: ReaderReflection.ReaderT
                                  (GHC.IORef.IORef GHC.Types.Int)
                                  (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                                  GHC.Types.Int
                                  ~#
                                (forall s_any.
                                 Data.Reflection.Reifies * s_any (GHC.IORef.IORef GHC.Types.Int) =>
                                 ReaderReflection.Tag
                                   (GHC.IORef.IORef GHC.Types.Int)
                                   s_any
                                   (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                                   GHC.Types.Int)))
                      @ s_any eta_B1 } in
                let {
                  lvl2_s1i8 :: Eval1.Value
                  [LclId]
                  lvl2_s1i8 =
                    (eta_B1
                     `cast` (<Data.Reflection.NTCo:Reifies <*> <s_any> <Eval1.Value>>
                             :: Data.Reflection.Reifies * s_any Eval1.Value
                                  ~#
                                (forall (proxy_apx :: * -> *). proxy_apx s_any -> Eval1.Value)))
                      @ (Data.Proxy.Proxy *) (Data.Proxy.Proxy @ * @ s_any) } in
                (\ (@ s1_Xry)
                   ($dReifies_XrA
                      :: Data.Reflection.Reifies
                           * s1_Xry (GHC.IORef.IORef GHC.Types.Int))
                   (s_aL4 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
                   case (((a12_s13s
                           `cast` (<ReaderReflection.NTCo:Tag
                                      <GHC.IORef.IORef GHC.Types.Int>
                                      <s_any>
                                      <ReaderReflection.ReaderT
                                         Eval1.Value
                                         GHC.Types.IO>> <GHC.Types.Int> ; <ReaderReflection.NTCo:ReaderT
                                                                             <GHC.IORef.IORef
                                                                                GHC.Types.Int>
                                                                             <GHC.Types.IO>
                                                                             <GHC.Types.Int>>
                                   :: ReaderReflection.Tag
                                        (GHC.IORef.IORef GHC.Types.Int)
                                        s_any
                                        (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                                        GHC.Types.Int
                                        ~#
                                      (forall s_any.
                                       Data.Reflection.Reifies
                                         * s_any (GHC.IORef.IORef GHC.Types.Int) =>
                                       ReaderReflection.Tag
                                         (GHC.IORef.IORef GHC.Types.Int)
                                         s_any
                                         GHC.Types.IO
                                         GHC.Types.Int)))
                            @ s1_Xry $dReifies_XrA)
                         `cast` (<ReaderReflection.NTCo:Tag
                                    <GHC.IORef.IORef GHC.Types.Int>
                                    <s1_Xry>
                                    <GHC.Types.IO>> <GHC.Types.Int> ; <GHC.Types.NTCo:IO
                                                                         <GHC.Types.Int>>
                                 :: ReaderReflection.Tag
                                      (GHC.IORef.IORef GHC.Types.Int)
                                      s1_Xry
                                      GHC.Types.IO
                                      GHC.Types.Int
                                      ~#
                                    (GHC.Prim.State# GHC.Prim.RealWorld
                                     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #))))
                          s_aL4
                   of _ { (# ipv_aL7, ipv1_aL8 #) ->
                   case lvl2_s1i8
                        `cast` (<GHC.IORef.NTCo:IORef> <GHC.Types.Int>
                                :: GHC.IORef.IORef GHC.Types.Int
                                     ~#
                                   GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int)
                   of _ { GHC.STRef.STRef var#_aLj ->
                   case GHC.Prim.readMutVar#
                          @ GHC.Prim.RealWorld @ GHC.Types.Int var#_aLj ipv_aL7
                   of _ { (# ipv2_XM0, ipv3_XM2 #) ->
                   case ipv1_aL8 of _ { GHC.Types.I# x1_a10D ->
                   case ipv3_XM2 of _ { GHC.Types.I# y_a10H ->
                   case GHC.Prim.writeMutVar#
                          @ GHC.Prim.RealWorld
                          @ GHC.Types.Int
                          var#_aLj
                          (GHC.Types.I# (GHC.Prim.+# x1_a10D y_a10H))
                          ipv2_XM0
                   of s2#_a12g { __DEFAULT ->
                   (# s2#_a12g, children_aTn #)
                   }
                   }
                   }
                   }
                   }
                   })
                `cast` ((forall s1_Xry.
                         <Data.Reflection.Reifies * s1_Xry (GHC.IORef.IORef GHC.Types.Int)>
                         -> Sym <(GHC.Types.NTCo:IO <[OptimizeMonadTrans.Tree]>)> ; Sym
                                                                                      <(ReaderReflection.NTCo:Tag
                                                                                          <GHC.IORef.IORef
                                                                                             GHC.Types.Int>
                                                                                          <s1_Xry>
                                                                                          <GHC.Types.IO>)> <[OptimizeMonadTrans.Tree]>) ; (Sym
                                                                                                                                             <(ReaderReflection.NTCo:ReaderT
                                                                                                                                                 <GHC.IORef.IORef
                                                                                                                                                    GHC.Types.Int>
                                                                                                                                                 <GHC.Types.IO>
                                                                                                                                                 <[OptimizeMonadTrans.Tree]>)> ; Sym
                                                                                                                                                                                   <(ReaderReflection.NTCo:Tag
                                                                                                                                                                                       <GHC.IORef.IORef
                                                                                                                                                                                          GHC.Types.Int>
                                                                                                                                                                                       <s_any>
                                                                                                                                                                                       <ReaderReflection.ReaderT
                                                                                                                                                                                          Eval1.Value
                                                                                                                                                                                          GHC.Types.IO>)> <[OptimizeMonadTrans.Tree]>)
                        :: (forall s1_Xry.
                            Data.Reflection.Reifies * s1_Xry (GHC.IORef.IORef GHC.Types.Int) =>
                            GHC.Prim.State# GHC.Prim.RealWorld
                            -> (# GHC.Prim.State# GHC.Prim.RealWorld,
                                  [OptimizeMonadTrans.Tree] #))
                             ~#
                           ReaderReflection.Tag
                             (GHC.IORef.IORef GHC.Types.Int)
                             s_any
                             (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                             [OptimizeMonadTrans.Tree]);
              OptimizeMonadTrans.Leaf ->
                lvl_r1iO
                `cast` ((forall s1_Xo0.
                         <Data.Reflection.Reifies * s1_Xo0 (GHC.IORef.IORef GHC.Types.Int)>
                         -> Sym <(GHC.Types.NTCo:IO <[OptimizeMonadTrans.Tree]>)> ; Sym
                                                                                      <(ReaderReflection.NTCo:Tag
                                                                                          <GHC.IORef.IORef
                                                                                             GHC.Types.Int>
                                                                                          <s1_Xo0>
                                                                                          <GHC.Types.IO>)> <[OptimizeMonadTrans.Tree]>) ; (Sym
                                                                                                                                             <(ReaderReflection.NTCo:ReaderT
                                                                                                                                                 <GHC.IORef.IORef
                                                                                                                                                    GHC.Types.Int>
                                                                                                                                                 <GHC.Types.IO>
                                                                                                                                                 <[OptimizeMonadTrans.Tree]>)> ; Sym
                                                                                                                                                                                   <(ReaderReflection.NTCo:Tag
                                                                                                                                                                                       <GHC.IORef.IORef
                                                                                                                                                                                          GHC.Types.Int>
                                                                                                                                                                                       <s_any>
                                                                                                                                                                                       <ReaderReflection.ReaderT
                                                                                                                                                                                          Eval1.Value
                                                                                                                                                                                          GHC.Types.IO>)> <[OptimizeMonadTrans.Tree]>)
                        :: (forall s1_Xo0.
                            Data.Reflection.Reifies * s1_Xo0 (GHC.IORef.IORef GHC.Types.Int) =>
                            GHC.Prim.State# GHC.Prim.RealWorld
                            -> (# GHC.Prim.State# GHC.Prim.RealWorld,
                                  [OptimizeMonadTrans.Tree] #))
                             ~#
                           ReaderReflection.Tag
                             (GHC.IORef.IORef GHC.Types.Int)
                             s_any
                             (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                             [OptimizeMonadTrans.Tree])
            } } in
        (\ (@ s1_Xrv)
           ($dReifies_Xrx
              :: Data.Reflection.Reifies
                   * s1_Xrv (GHC.IORef.IORef GHC.Types.Int))
           (s_aL4 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
           case (((a11_s13y
                   `cast` (<ReaderReflection.NTCo:Tag
                              <GHC.IORef.IORef GHC.Types.Int>
                              <s_any>
                              <ReaderReflection.ReaderT
                                 Eval1.Value
                                 GHC.Types.IO>> <[OptimizeMonadTrans.Tree]> ; <ReaderReflection.NTCo:ReaderT
                                                                                 <GHC.IORef.IORef
                                                                                    GHC.Types.Int>
                                                                                 <GHC.Types.IO>
                                                                                 <[OptimizeMonadTrans.Tree]>>
                           :: ReaderReflection.Tag
                                (GHC.IORef.IORef GHC.Types.Int)
                                s_any
                                (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                                [OptimizeMonadTrans.Tree]
                                ~#
                              (forall s_any.
                               Data.Reflection.Reifies * s_any (GHC.IORef.IORef GHC.Types.Int) =>
                               ReaderReflection.Tag
                                 (GHC.IORef.IORef GHC.Types.Int)
                                 s_any
                                 GHC.Types.IO
                                 [OptimizeMonadTrans.Tree])))
                    @ s1_Xrv $dReifies_Xrx)
                 `cast` (<ReaderReflection.NTCo:Tag
                            <GHC.IORef.IORef GHC.Types.Int>
                            <s1_Xrv>
                            <GHC.Types.IO>> <[OptimizeMonadTrans.Tree]> ; <GHC.Types.NTCo:IO
                                                                             <[OptimizeMonadTrans.Tree]>>
                         :: ReaderReflection.Tag
                              (GHC.IORef.IORef GHC.Types.Int)
                              s1_Xrv
                              GHC.Types.IO
                              [OptimizeMonadTrans.Tree]
                              ~#
                            (GHC.Prim.State# GHC.Prim.RealWorld
                             -> (# GHC.Prim.State# GHC.Prim.RealWorld,
                                   [OptimizeMonadTrans.Tree] #))))
                  s_aL4
           of _ { (# ipv_aL7, ipv1_aL8 #) ->
           ((((a8_r1iQ
                 (GHC.Base.++ @ OptimizeMonadTrans.Tree ipv1_aL8 xs_aTk)
                 @ s_any
                 eta_B1)
              `cast` (<ReaderReflection.NTCo:Tag
                         <GHC.IORef.IORef GHC.Types.Int>
                         <s_any>
                         <ReaderReflection.ReaderT
                            Eval1.Value GHC.Types.IO>> <()> ; <ReaderReflection.NTCo:ReaderT
                                                                 <GHC.IORef.IORef GHC.Types.Int>
                                                                 <GHC.Types.IO>
                                                                 <()>>
                      :: ReaderReflection.Tag
                           (GHC.IORef.IORef GHC.Types.Int)
                           s_any
                           (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                           ()
                           ~#
                         (forall s_any.
                          Data.Reflection.Reifies * s_any (GHC.IORef.IORef GHC.Types.Int) =>
                          ReaderReflection.Tag
                            (GHC.IORef.IORef GHC.Types.Int) s_any GHC.Types.IO ())))
               @ s1_Xrv $dReifies_Xrx)
            `cast` (<ReaderReflection.NTCo:Tag
                       <GHC.IORef.IORef GHC.Types.Int>
                       <s1_Xrv>
                       <GHC.Types.IO>> <()> ; <GHC.Types.NTCo:IO <()>>
                    :: ReaderReflection.Tag
                         (GHC.IORef.IORef GHC.Types.Int) s1_Xrv GHC.Types.IO ()
                         ~#
                       (GHC.Prim.State# GHC.Prim.RealWorld
                        -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #))))
             ipv_aL7
           })
        `cast` ((forall s1_Xrv.
                 <Data.Reflection.Reifies * s1_Xrv (GHC.IORef.IORef GHC.Types.Int)>
                 -> Sym <(GHC.Types.NTCo:IO <()>)> ; Sym
                                                       <(ReaderReflection.NTCo:Tag
                                                           <GHC.IORef.IORef GHC.Types.Int>
                                                           <s1_Xrv>
                                                           <GHC.Types.IO>)> <()>) ; (Sym
                                                                                       <(ReaderReflection.NTCo:ReaderT
                                                                                           <GHC.IORef.IORef
                                                                                              GHC.Types.Int>
                                                                                           <GHC.Types.IO>
                                                                                           <()>)> ; Sym
                                                                                                      <(ReaderReflection.NTCo:Tag
                                                                                                          <GHC.IORef.IORef
                                                                                                             GHC.Types.Int>
                                                                                                          <s_any>
                                                                                                          <ReaderReflection.ReaderT
                                                                                                             Eval1.Value
                                                                                                             GHC.Types.IO>)> <()>)
                :: (forall s1_Xrv.
                    Data.Reflection.Reifies * s1_Xrv (GHC.IORef.IORef GHC.Types.Int) =>
                    GHC.Prim.State# GHC.Prim.RealWorld
                    -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #))
                     ~#
                   ReaderReflection.Tag
                     (GHC.IORef.IORef GHC.Types.Int)
                     s_any
                     (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                     ())
    }
end Rec }

a9_r1iR :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a9_r1iR =
  GHC.Types.:
    @ OptimizeMonadTrans.Tree
    tree_rPN
    (GHC.Types.[] @ OptimizeMonadTrans.Tree)

a10_r1iS
  :: forall s_any.
     Data.Reflection.Reifies * s_any Eval1.Value =>
     ReaderReflection.Tag
       Eval1.Value
       s_any
       (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
       ()
[GblId, Arity=1, Str=DmdType]
a10_r1iS = a8_r1iQ a9_r1iR

OptimizeMonadTrans.example [InlPrag=NOINLINE] :: Eval1.Eval ()
[GblId, Str=DmdType]
OptimizeMonadTrans.example =
  a10_r1iS
  `cast` (Sym
            <(ReaderReflection.NTCo:ReaderT
                <Eval1.Value>
                <ReaderReflection.ReaderT Eval1.Value GHC.Types.IO>
                <()>)>
          :: (forall s_any.
              Data.Reflection.Reifies * s_any Eval1.Value =>
              ReaderReflection.Tag
                Eval1.Value
                s_any
                (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO)
                ())
               ~#
             ReaderReflection.ReaderT
               Eval1.Value (ReaderReflection.ReaderT Eval1.Value GHC.Types.IO) ())

OptimizeMonadTrans.main1
  :: GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #)
[GblId,
 Arity=1,
 Str=DmdType L,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=1, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=IF_ARGS [0] 110 0}]
OptimizeMonadTrans.main1 =
  \ (s_aL4 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    case Eval1.runEval1 @ () OptimizeMonadTrans.example s_aL4
    of _ { (# ipv_aL7, ipv1_aL8 #) ->
    GHC.IO.Handle.Text.hPutStr2
      GHC.IO.Handle.FD.stdout
      (GHC.Show.$fShowInt_$cshow ipv1_aL8)
      GHC.Types.True
      ipv_aL7
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



