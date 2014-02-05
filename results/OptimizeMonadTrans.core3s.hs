[1 of 2] Compiling Eval3            ( Eval3.hs, build/Eval3.o )

==================== Tidy Core ====================
Result size of Tidy Core = {terms: 133, types: 230, coercions: 148}

Eval3.run1 :: forall a_g. Eval3.Eval a_g -> Eval3.Eval a_g
[GblId,
 Arity=1,
 Caf=NoCafRefs,
 Str=DmdType S,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=1, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval3.run1 = \ (@ a_g) (ds_dhV :: Eval3.Eval a_g) -> ds_dhV

Eval3.run
  :: forall a_afw.
     Eval3.Eval a_afw
     -> Eval3.Value -> Eval3.Value -> GHC.Types.IO a_afw
[GblId[[RecSel]],
 Arity=1,
 Caf=NoCafRefs,
 Str=DmdType S,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval3.run =
  Eval3.run1
  `cast` (forall a_g. <Eval3.Eval a_g> -> <Eval3.NTCo:Eval <a_g>>
          :: (forall a_g. Eval3.Eval a_g -> Eval3.Eval a_g)
               ~#
             (forall a_g.
              Eval3.Eval a_g -> Eval3.Value -> Eval3.Value -> GHC.Types.IO a_g))

Eval3.$fMonadIOEval1
  :: forall a_tA.
     GHC.Types.IO a_tA
     -> Eval3.Value -> Eval3.Value -> GHC.Types.IO a_tA
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType SAA,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ a_tA) (m_afN [Occ=Once] :: GHC.Types.IO a_tA) _ _ ->
                 m_afN}]
Eval3.$fMonadIOEval1 =
  \ (@ a_tA) (m_afN :: GHC.Types.IO a_tA) _ _ -> m_afN

Eval3.$fMonadIOEval_$cliftIO
  :: forall a_ahg. GHC.Types.IO a_ahg -> Eval3.Eval a_ahg
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType SAA,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Eval3.$fMonadIOEval1
               `cast` (forall a_tA.
                       <GHC.Types.IO a_tA> -> Sym <(Eval3.NTCo:Eval <a_tA>)>
                       :: (forall a_tA.
                           GHC.Types.IO a_tA
                           -> Eval3.Value -> Eval3.Value -> GHC.Types.IO a_tA)
                            ~#
                          (forall a_tA. GHC.Types.IO a_tA -> Eval3.Eval a_tA))}]
Eval3.$fMonadIOEval_$cliftIO =
  Eval3.$fMonadIOEval1
  `cast` (forall a_tA.
          <GHC.Types.IO a_tA> -> Sym <(Eval3.NTCo:Eval <a_tA>)>
          :: (forall a_tA.
              GHC.Types.IO a_tA
              -> Eval3.Value -> Eval3.Value -> GHC.Types.IO a_tA)
               ~#
             (forall a_tA. GHC.Types.IO a_tA -> Eval3.Eval a_tA))

Eval3.ask3
  :: Eval3.Value
     -> Eval3.Value
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval3.Value #)
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType LAL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (x_afJ [Occ=Once] :: Eval3.Value)
                 _
                 (s_ajq [Occ=Once] :: GHC.Prim.State# GHC.Prim.RealWorld) ->
                 (# s_ajq, x_afJ #)}]
Eval3.ask3 =
  \ (x_afJ :: Eval3.Value)
    _
    (s_ajq :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# s_ajq, x_afJ #)

Eval3.ask1 :: Eval3.Eval Eval3.Value
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType LAL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Eval3.ask3
               `cast` ((<Eval3.Value>
                        -> <Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <Eval3.Value>)>) ; Sym
                                                                                         <(Eval3.NTCo:Eval
                                                                                             <Eval3.Value>)>
                       :: (Eval3.Value
                           -> Eval3.Value
                           -> GHC.Prim.State# GHC.Prim.RealWorld
                           -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval3.Value #))
                            ~#
                          Eval3.Eval Eval3.Value)}]
Eval3.ask1 =
  Eval3.ask3
  `cast` ((<Eval3.Value>
           -> <Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <Eval3.Value>)>) ; Sym
                                                                            <(Eval3.NTCo:Eval
                                                                                <Eval3.Value>)>
          :: (Eval3.Value
              -> Eval3.Value
              -> GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval3.Value #))
               ~#
             Eval3.Eval Eval3.Value)

Eval3.$fMonadEval2
  :: forall a_tC b_tD.
     Eval3.Eval a_tC
     -> (a_tC -> Eval3.Eval b_tD)
     -> Eval3.Value
     -> Eval3.Value
     -> GHC.Types.IO b_tD
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType LLL,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=IF_ARGS [0 60 0] 85 60}]
Eval3.$fMonadEval2 =
  \ (@ a_tC)
    (@ b_tD)
    (m_afP :: Eval3.Eval a_tC)
    (k_afQ :: a_tC -> Eval3.Eval b_tD)
    (x_afR :: Eval3.Value) ->
    let {
      b_siW [Dmd=Just L] :: Eval3.Value -> GHC.Types.IO a_tC
      [LclId, Str=DmdType]
      b_siW =
        (m_afP
         `cast` (<Eval3.NTCo:Eval <a_tC>>
                 :: Eval3.Eval a_tC
                      ~#
                    (Eval3.Value -> Eval3.Value -> GHC.Types.IO a_tC)))
          x_afR } in
    (\ (y_afT :: Eval3.Value)
       (s_ajB :: GHC.Prim.State# GHC.Prim.RealWorld) ->
       case ((b_siW y_afT)
             `cast` (<GHC.Types.NTCo:IO <a_tC>>
                     :: GHC.Types.IO a_tC
                          ~#
                        (GHC.Prim.State# GHC.Prim.RealWorld
                         -> (# GHC.Prim.State# GHC.Prim.RealWorld, a_tC #))))
              s_ajB
       of _ { (# ipv_ajE, ipv1_ajF #) ->
       ((((k_afQ ipv1_ajF)
          `cast` (<Eval3.NTCo:Eval <b_tD>>
                  :: Eval3.Eval b_tD
                       ~#
                     (Eval3.Value -> Eval3.Value -> GHC.Types.IO b_tD)))
           x_afR y_afT)
        `cast` (<GHC.Types.NTCo:IO <b_tD>>
                :: GHC.Types.IO b_tD
                     ~#
                   (GHC.Prim.State# GHC.Prim.RealWorld
                    -> (# GHC.Prim.State# GHC.Prim.RealWorld, b_tD #))))
         ipv_ajE
       })
    `cast` (<Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <b_tD>)>
            :: (Eval3.Value
                -> GHC.Prim.State# GHC.Prim.RealWorld
                -> (# GHC.Prim.State# GHC.Prim.RealWorld, b_tD #))
                 ~#
               (Eval3.Value -> GHC.Types.IO b_tD))

Eval3.$fMonadEval_$c>>=
  :: forall a_age b_agf.
     Eval3.Eval a_age -> (a_age -> Eval3.Eval b_agf) -> Eval3.Eval b_agf
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType LLL,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval3.$fMonadEval_$c>>= =
  Eval3.$fMonadEval2
  `cast` (forall a_tC b_tD.
          <Eval3.Eval a_tC>
          -> <a_tC -> Eval3.Eval b_tD> -> Sym <(Eval3.NTCo:Eval <b_tD>)>
          :: (forall a_tC b_tD.
              Eval3.Eval a_tC
              -> (a_tC -> Eval3.Eval b_tD)
              -> Eval3.Value
              -> Eval3.Value
              -> GHC.Types.IO b_tD)
               ~#
             (forall a_tC b_tD.
              Eval3.Eval a_tC -> (a_tC -> Eval3.Eval b_tD) -> Eval3.Eval b_tD))

Eval3.$fMonadEval1
  :: forall a_tN.
     a_tN
     -> Eval3.Value
     -> Eval3.Value
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, a_tN #)
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType LAAL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=4, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ a_tN)
                 (a1_afO [Occ=Once] :: a_tN)
                 _
                 _
                 (eta2_B1 [Occ=Once] :: GHC.Prim.State# GHC.Prim.RealWorld) ->
                 (# eta2_B1, a1_afO #)}]
Eval3.$fMonadEval1 =
  \ (@ a_tN)
    (a1_afO :: a_tN)
    _
    _
    (eta2_B1 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# eta2_B1, a1_afO #)

Eval3.$fMonadEval_$creturn
  :: forall a_ah5. a_ah5 -> Eval3.Eval a_ah5
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType LAAL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Eval3.$fMonadEval1
               `cast` (forall a_tN.
                       <a_tN>
                       -> (<Eval3.Value>
                           -> <Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <a_tN>)>) ; Sym
                                                                                     <(Eval3.NTCo:Eval
                                                                                         <a_tN>)>
                       :: (forall a_tN.
                           a_tN
                           -> Eval3.Value
                           -> Eval3.Value
                           -> GHC.Prim.State# GHC.Prim.RealWorld
                           -> (# GHC.Prim.State# GHC.Prim.RealWorld, a_tN #))
                            ~#
                          (forall a_tN. a_tN -> Eval3.Eval a_tN))}]
Eval3.$fMonadEval_$creturn =
  Eval3.$fMonadEval1
  `cast` (forall a_tN.
          <a_tN>
          -> (<Eval3.Value>
              -> <Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <a_tN>)>) ; Sym
                                                                        <(Eval3.NTCo:Eval <a_tN>)>
          :: (forall a_tN.
              a_tN
              -> Eval3.Value
              -> Eval3.Value
              -> GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, a_tN #))
               ~#
             (forall a_tN. a_tN -> Eval3.Eval a_tN))

Eval3.$fMonadEval_$cfail
  :: forall a_ahH. GHC.Base.String -> Eval3.Eval a_ahH
[GblId, Arity=1, Str=DmdType Sb]
Eval3.$fMonadEval_$cfail =
  \ (@ a_air) (eta_B1 :: [GHC.Types.Char]) ->
    GHC.Err.error @ (Eval3.Eval a_air) eta_B1

a_rl1
  :: forall a_agY b_agZ.
     Eval3.Eval a_agY
     -> Eval3.Eval b_agZ
     -> Eval3.Value
     -> Eval3.Value
     -> GHC.Types.IO b_agZ
[GblId, Arity=3, Caf=NoCafRefs, Str=DmdType LLL]
a_rl1 =
  \ (@ a_agY)
    (@ b_agZ)
    (eta_B2 :: Eval3.Eval a_agY)
    (eta1_B1 :: Eval3.Eval b_agZ)
    (eta2_X2 :: Eval3.Value) ->
    let {
      b_siW [Dmd=Just L] :: Eval3.Value -> GHC.Types.IO a_agY
      [LclId, Str=DmdType]
      b_siW =
        (eta_B2
         `cast` (<Eval3.NTCo:Eval <a_agY>>
                 :: Eval3.Eval a_agY
                      ~#
                    (Eval3.Value -> Eval3.Value -> GHC.Types.IO a_agY)))
          eta2_X2 } in
    (\ (y_afT :: Eval3.Value)
       (s_ajB :: GHC.Prim.State# GHC.Prim.RealWorld) ->
       case ((b_siW y_afT)
             `cast` (<GHC.Types.NTCo:IO <a_agY>>
                     :: GHC.Types.IO a_agY
                          ~#
                        (GHC.Prim.State# GHC.Prim.RealWorld
                         -> (# GHC.Prim.State# GHC.Prim.RealWorld, a_agY #))))
              s_ajB
       of _ { (# ipv_ajE, _ #) ->
       (((eta1_B1
          `cast` (<Eval3.NTCo:Eval <b_agZ>>
                  :: Eval3.Eval b_agZ
                       ~#
                     (Eval3.Value -> Eval3.Value -> GHC.Types.IO b_agZ)))
           eta2_X2 y_afT)
        `cast` (<GHC.Types.NTCo:IO <b_agZ>>
                :: GHC.Types.IO b_agZ
                     ~#
                   (GHC.Prim.State# GHC.Prim.RealWorld
                    -> (# GHC.Prim.State# GHC.Prim.RealWorld, b_agZ #))))
         ipv_ajE
       })
    `cast` (<Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <b_agZ>)>
            :: (Eval3.Value
                -> GHC.Prim.State# GHC.Prim.RealWorld
                -> (# GHC.Prim.State# GHC.Prim.RealWorld, b_agZ #))
                 ~#
               (Eval3.Value -> GHC.Types.IO b_agZ))

Eval3.$fMonadEval_$c>> [InlPrag=INLINE (sat-args=2)]
  :: forall a_agY b_agZ.
     Eval3.Eval a_agY -> Eval3.Eval b_agZ -> Eval3.Eval b_agZ
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType LLL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=False,boring_ok=False)
         Tmpl= \ (@ a_aik)
                 (@ b_ail)
                 (m_aim [Occ=Once] :: Eval3.Eval a_aik)
                 (k_ain [Occ=OnceL] :: Eval3.Eval b_ail) ->
                 Eval3.$fMonadEval_$c>>= @ a_aik @ b_ail m_aim (\ _ -> k_ain)}]
Eval3.$fMonadEval_$c>> =
  a_rl1
  `cast` (forall a_agY b_agZ.
          <Eval3.Eval a_agY>
          -> <Eval3.Eval b_agZ> -> Sym <(Eval3.NTCo:Eval <b_agZ>)>
          :: (forall a_agY b_agZ.
              Eval3.Eval a_agY
              -> Eval3.Eval b_agZ
              -> Eval3.Value
              -> Eval3.Value
              -> GHC.Types.IO b_agZ)
               ~#
             (forall a_agY b_agZ.
              Eval3.Eval a_agY -> Eval3.Eval b_agZ -> Eval3.Eval b_agZ))

Eval3.$fMonadEval [InlPrag=[ALWAYS] CONLIKE]
  :: GHC.Base.Monad Eval3.Eval
[GblId[DFunId],
 Str=DmdType m,
 Unf=DFun(arity=0) GHC.Base.D:Monad [{Eval3.$fMonadEval_$c>>=},
                                     {Eval3.$fMonadEval_$c>>}, {Eval3.$fMonadEval_$creturn},
                                     {Eval3.$fMonadEval_$cfail}]]
Eval3.$fMonadEval =
  GHC.Base.D:Monad
    @ Eval3.Eval
    (Eval3.$fMonadEval2
     `cast` (forall a_X1l b_X1n.
             <Eval3.Eval a_X1l>
             -> <a_X1l -> Eval3.Eval b_X1n> -> Sym <(Eval3.NTCo:Eval <b_X1n>)>
             :: (forall a_X1l b_X1n.
                 Eval3.Eval a_X1l
                 -> (a_X1l -> Eval3.Eval b_X1n)
                 -> Eval3.Value
                 -> Eval3.Value
                 -> GHC.Types.IO b_X1n)
                  ~#
                (forall a_X1l b_X1n.
                 Eval3.Eval a_X1l
                 -> (a_X1l -> Eval3.Eval b_X1n) -> Eval3.Eval b_X1n)))
    Eval3.$fMonadEval_$c>>
    (Eval3.$fMonadEval1
     `cast` (forall a_X1p.
             <a_X1p>
             -> (<Eval3.Value>
                 -> <Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <a_X1p>)>) ; Sym
                                                                            <(Eval3.NTCo:Eval
                                                                                <a_X1p>)>
             :: (forall a_X1p.
                 a_X1p
                 -> Eval3.Value
                 -> Eval3.Value
                 -> GHC.Prim.State# GHC.Prim.RealWorld
                 -> (# GHC.Prim.State# GHC.Prim.RealWorld, a_X1p #))
                  ~#
                (forall a_X1p. a_X1p -> Eval3.Eval a_X1p)))
    Eval3.$fMonadEval_$cfail

Eval3.$fMonadIOEval [InlPrag=[ALWAYS] CONLIKE]
  :: Control.Monad.IO.Class.MonadIO Eval3.Eval
[GblId[DFunId],
 Str=DmdType m,
 Unf=DFun(arity=0) Control.Monad.IO.Class.D:MonadIO [{Eval3.$fMonadEval},
                                                     {Eval3.$fMonadIOEval_$cliftIO}]]
Eval3.$fMonadIOEval =
  Control.Monad.IO.Class.D:MonadIO
    @ Eval3.Eval
    Eval3.$fMonadEval
    (Eval3.$fMonadIOEval1
     `cast` (forall a_X1k.
             <GHC.Types.IO a_X1k> -> Sym <(Eval3.NTCo:Eval <a_X1k>)>
             :: (forall a_X1k.
                 GHC.Types.IO a_X1k
                 -> Eval3.Value -> Eval3.Value -> GHC.Types.IO a_X1k)
                  ~#
                (forall a_X1k. GHC.Types.IO a_X1k -> Eval3.Eval a_X1k)))

Eval3.runEval2 :: GHC.Types.Int
[GblId,
 Caf=NoCafRefs,
 Str=DmdType m,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=False, Expandable=True,
         Guidance=IF_ARGS [] 10 20}]
Eval3.runEval2 = GHC.Types.I# 0

Eval3.runEval1
  :: forall void_m.
     Eval3.Eval void_m
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #)
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType LL,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=IF_ARGS [0 0] 47 0}]
Eval3.runEval1 =
  \ (@ void_m)
    (m_afL :: Eval3.Eval void_m)
    (eta_XI :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    case GHC.Prim.newMutVar#
           @ GHC.Types.Int @ GHC.Prim.RealWorld Eval3.runEval2 eta_XI
    of _ { (# ipv_ajS, ipv1_ajT #) ->
    let {
      a1_sk0 :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
      [LclId, Str=DmdType m]
      a1_sk0 =
        GHC.STRef.STRef @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_ajT } in
    case (((m_afL
            `cast` (<Eval3.NTCo:Eval <void_m>>
                    :: Eval3.Eval void_m
                         ~#
                       (Eval3.Value -> Eval3.Value -> GHC.Types.IO void_m)))
             (a1_sk0
              `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int>
                      :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                           ~#
                         GHC.IORef.IORef GHC.Types.Int))
             (a1_sk0
              `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int>
                      :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                           ~#
                         GHC.IORef.IORef GHC.Types.Int)))
          `cast` (<GHC.Types.NTCo:IO <void_m>>
                  :: GHC.Types.IO void_m
                       ~#
                     (GHC.Prim.State# GHC.Prim.RealWorld
                      -> (# GHC.Prim.State# GHC.Prim.RealWorld, void_m #))))
           ipv_ajS
    of _ { (# ipv2_XkI, _ #) ->
    GHC.Prim.readMutVar#
      @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_ajT ipv2_XkI
    }
    }

Eval3.runEval
  :: forall void_afI.
     Eval3.Eval void_afI -> GHC.Types.IO GHC.Types.Int
[GblId,
 Arity=2,
 Caf=NoCafRefs,
 Str=DmdType LL,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval3.runEval =
  Eval3.runEval1
  `cast` (forall void_m.
          <Eval3.Eval void_m> -> Sym <(GHC.Types.NTCo:IO <GHC.Types.Int>)>
          :: (forall void_m.
              Eval3.Eval void_m
              -> GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #))
               ~#
             (forall void_m. Eval3.Eval void_m -> GHC.Types.IO GHC.Types.Int))

Eval3.ask4
  :: Eval3.Value
     -> Eval3.Value
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval3.Value #)
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType ALL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ _
                 (y_afK [Occ=Once] :: Eval3.Value)
                 (s_ajq [Occ=Once] :: GHC.Prim.State# GHC.Prim.RealWorld) ->
                 (# s_ajq, y_afK #)}]
Eval3.ask4 =
  \ _
    (y_afK :: Eval3.Value)
    (s_ajq :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# s_ajq, y_afK #)

Eval3.ask2 :: Eval3.Eval Eval3.Value
[GblId,
 Arity=3,
 Caf=NoCafRefs,
 Str=DmdType ALL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Eval3.ask4
               `cast` ((<Eval3.Value>
                        -> <Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <Eval3.Value>)>) ; Sym
                                                                                         <(Eval3.NTCo:Eval
                                                                                             <Eval3.Value>)>
                       :: (Eval3.Value
                           -> Eval3.Value
                           -> GHC.Prim.State# GHC.Prim.RealWorld
                           -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval3.Value #))
                            ~#
                          Eval3.Eval Eval3.Value)}]
Eval3.ask2 =
  Eval3.ask4
  `cast` ((<Eval3.Value>
           -> <Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <Eval3.Value>)>) ; Sym
                                                                            <(Eval3.NTCo:Eval
                                                                                <Eval3.Value>)>
          :: (Eval3.Value
              -> Eval3.Value
              -> GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, Eval3.Value #))
               ~#
             Eval3.Eval Eval3.Value)



[2 of 2] Compiling OptimizeMonadTrans ( OptimizeMonadTrans.hs, build/OptimizeMonadTrans.o )

==================== Tidy Core ====================
Result size of Tidy Core = {terms: 179, types: 224, coercions: 73}

a_rTn :: GHC.Types.Int
[GblId, Caf=NoCafRefs, Str=DmdType m]
a_rTn = GHC.Types.I# 1

a1_rTo
  :: Eval3.Value
     -> Eval3.Value
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #)
[GblId, Arity=3, Caf=NoCafRefs, Str=DmdType AAL]
a1_rTo =
  \ _ _ (eta2_X1b :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# eta2_X1b, a_rTn #)

a2_rTp :: GHC.Types.Int
[GblId, Caf=NoCafRefs, Str=DmdType m]
a2_rTp = GHC.Types.I# 2

a3_rTq
  :: Eval3.Value
     -> Eval3.Value
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #)
[GblId, Arity=3, Caf=NoCafRefs, Str=DmdType AAL]
a3_rTq =
  \ _ _ (eta2_X1v :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# eta2_X1v, a2_rTp #)

a4_rTr :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a4_rTr =
  GHC.Types.:
    @ OptimizeMonadTrans.Tree
    OptimizeMonadTrans.Leaf
    (GHC.Types.[] @ OptimizeMonadTrans.Tree)

a5_rTs :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a5_rTs =
  GHC.Types.:
    @ OptimizeMonadTrans.Tree OptimizeMonadTrans.Leaf a4_rTr

a6_rTt :: OptimizeMonadTrans.Tree
[GblId, Caf=NoCafRefs, Str=DmdType]
a6_rTt =
  OptimizeMonadTrans.Branch
    (a3_rTq
     `cast` ((<Eval3.Value>
              -> <Eval3.Value>
              -> Sym <(GHC.Types.NTCo:IO <GHC.Types.Int>)>) ; Sym
                                                                <(Eval3.NTCo:Eval <GHC.Types.Int>)>
             :: (Eval3.Value
                 -> Eval3.Value
                 -> GHC.Prim.State# GHC.Prim.RealWorld
                 -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #))
                  ~#
                Eval3.Eval GHC.Types.Int))
    a5_rTs

a7_rTu :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a7_rTu = GHC.Types.: @ OptimizeMonadTrans.Tree a6_rTt a4_rTr

tree_rqO :: OptimizeMonadTrans.Tree
[GblId, Caf=NoCafRefs, Str=DmdType]
tree_rqO =
  OptimizeMonadTrans.Branch
    (a1_rTo
     `cast` ((<Eval3.Value>
              -> <Eval3.Value>
              -> Sym <(GHC.Types.NTCo:IO <GHC.Types.Int>)>) ; Sym
                                                                <(Eval3.NTCo:Eval <GHC.Types.Int>)>
             :: (Eval3.Value
                 -> Eval3.Value
                 -> GHC.Prim.State# GHC.Prim.RealWorld
                 -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #))
                  ~#
                Eval3.Eval GHC.Types.Int))
    a7_rTu

lvl_rTv
  :: Eval3.Value
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld,
           [OptimizeMonadTrans.Tree] #)
[GblId, Arity=2, Caf=NoCafRefs]
lvl_rTv =
  \ (y_afT :: Eval3.Value)
    (s_ajB :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    case y_afT
         `cast` (<GHC.IORef.NTCo:IORef> <GHC.Types.Int>
                 :: GHC.IORef.IORef GHC.Types.Int
                      ~#
                    GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int)
    of _ { GHC.STRef.STRef var#_ak7 ->
    case GHC.Prim.readMutVar#
           @ GHC.Prim.RealWorld @ GHC.Types.Int var#_ak7 s_ajB
    of _ { (# ipv_ajE, ipv1_ajF #) ->
    case ipv1_ajF of _ { GHC.Types.I# x_aBu ->
    case GHC.Prim.writeMutVar#
           @ GHC.Prim.RealWorld
           @ GHC.Types.Int
           var#_ak7
           (GHC.Types.I# (GHC.Prim.+# x_aBu 1))
           ipv_ajE
    of s2#_aCT { __DEFAULT ->
    (# s2#_aCT, GHC.Types.[] @ OptimizeMonadTrans.Tree #)
    }
    }
    }
    }

lvl1_rTw
  :: Eval3.Value
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #)
[GblId, Arity=2, Caf=NoCafRefs]
lvl1_rTw =
  \ _ (eta2_X27 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# eta2_X27, GHC.Tuple.() #)

Rec {
a8_rTx
  :: [OptimizeMonadTrans.Tree]
     -> Eval3.Value -> Eval3.Value -> GHC.Types.IO ()
[GblId, Arity=2, Caf=NoCafRefs, Str=DmdType SL]
a8_rTx =
  \ (ds_dzZ :: [OptimizeMonadTrans.Tree]) (eta_B1 :: Eval3.Value) ->
    case ds_dzZ of _ {
      [] ->
        lvl1_rTw
        `cast` (<Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <()>)>
                :: (Eval3.Value
                    -> GHC.Prim.State# GHC.Prim.RealWorld
                    -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #))
                     ~#
                   (Eval3.Value -> GHC.Types.IO ()));
      : x_auk xs_aul ->
        let {
          b_siW [Dmd=Just L]
            :: Eval3.Value -> GHC.Types.IO [OptimizeMonadTrans.Tree]
          [LclId, Str=DmdType]
          b_siW =
            case x_auk of _ {
              OptimizeMonadTrans.Branch action_aun children_auo ->
                let {
                  b1_Xjr [Dmd=Just L] :: Eval3.Value -> GHC.Types.IO GHC.Types.Int
                  [LclId, Str=DmdType]
                  b1_Xjr =
                    (action_aun
                     `cast` (<Eval3.NTCo:Eval <GHC.Types.Int>>
                             :: Eval3.Eval GHC.Types.Int
                                  ~#
                                (Eval3.Value -> Eval3.Value -> GHC.Types.IO GHC.Types.Int)))
                      eta_B1 } in
                (\ (y_afT :: Eval3.Value)
                   (s_ajB :: GHC.Prim.State# GHC.Prim.RealWorld) ->
                   case ((b1_Xjr y_afT)
                         `cast` (<GHC.Types.NTCo:IO <GHC.Types.Int>>
                                 :: GHC.Types.IO GHC.Types.Int
                                      ~#
                                    (GHC.Prim.State# GHC.Prim.RealWorld
                                     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #))))
                          s_ajB
                   of _ { (# ipv_ajE, ipv1_ajF #) ->
                   case eta_B1
                        `cast` (<GHC.IORef.NTCo:IORef> <GHC.Types.Int>
                                :: GHC.IORef.IORef GHC.Types.Int
                                     ~#
                                   GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int)
                   of _ { GHC.STRef.STRef var#_ak7 ->
                   case GHC.Prim.readMutVar#
                          @ GHC.Prim.RealWorld @ GHC.Types.Int var#_ak7 ipv_ajE
                   of _ { (# ipv2_Xkj, ipv3_Xkl #) ->
                   case ipv1_ajF of _ { GHC.Types.I# x1_aBu ->
                   case ipv3_Xkl of _ { GHC.Types.I# y1_aBy ->
                   case GHC.Prim.writeMutVar#
                          @ GHC.Prim.RealWorld
                          @ GHC.Types.Int
                          var#_ak7
                          (GHC.Types.I# (GHC.Prim.+# x1_aBu y1_aBy))
                          ipv2_Xkj
                   of s2#_aCT { __DEFAULT ->
                   (# s2#_aCT, children_auo #)
                   }
                   }
                   }
                   }
                   }
                   })
                `cast` (<Eval3.Value>
                        -> Sym <(GHC.Types.NTCo:IO <[OptimizeMonadTrans.Tree]>)>
                        :: (Eval3.Value
                            -> GHC.Prim.State# GHC.Prim.RealWorld
                            -> (# GHC.Prim.State# GHC.Prim.RealWorld,
                                  [OptimizeMonadTrans.Tree] #))
                             ~#
                           (Eval3.Value -> GHC.Types.IO [OptimizeMonadTrans.Tree]));
              OptimizeMonadTrans.Leaf ->
                lvl_rTv
                `cast` (<Eval3.Value>
                        -> Sym <(GHC.Types.NTCo:IO <[OptimizeMonadTrans.Tree]>)>
                        :: (Eval3.Value
                            -> GHC.Prim.State# GHC.Prim.RealWorld
                            -> (# GHC.Prim.State# GHC.Prim.RealWorld,
                                  [OptimizeMonadTrans.Tree] #))
                             ~#
                           (Eval3.Value -> GHC.Types.IO [OptimizeMonadTrans.Tree]))
            } } in
        (\ (y_afT :: Eval3.Value)
           (s_ajB :: GHC.Prim.State# GHC.Prim.RealWorld) ->
           case ((b_siW y_afT)
                 `cast` (<GHC.Types.NTCo:IO <[OptimizeMonadTrans.Tree]>>
                         :: GHC.Types.IO [OptimizeMonadTrans.Tree]
                              ~#
                            (GHC.Prim.State# GHC.Prim.RealWorld
                             -> (# GHC.Prim.State# GHC.Prim.RealWorld,
                                   [OptimizeMonadTrans.Tree] #))))
                  s_ajB
           of _ { (# ipv_ajE, ipv1_ajF #) ->
           ((a8_rTx
               (GHC.Base.++ @ OptimizeMonadTrans.Tree ipv1_ajF xs_aul)
               eta_B1
               y_afT)
            `cast` (<GHC.Types.NTCo:IO <()>>
                    :: GHC.Types.IO ()
                         ~#
                       (GHC.Prim.State# GHC.Prim.RealWorld
                        -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #))))
             ipv_ajE
           })
        `cast` (<Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <()>)>
                :: (Eval3.Value
                    -> GHC.Prim.State# GHC.Prim.RealWorld
                    -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #))
                     ~#
                   (Eval3.Value -> GHC.Types.IO ()))
    }
end Rec }

a9_rTy :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a9_rTy =
  GHC.Types.:
    @ OptimizeMonadTrans.Tree
    tree_rqO
    (GHC.Types.[] @ OptimizeMonadTrans.Tree)

a10_rTz :: Eval3.Value -> Eval3.Value -> GHC.Types.IO ()
[GblId, Arity=1, Str=DmdType]
a10_rTz = a8_rTx a9_rTy

OptimizeMonadTrans.example [InlPrag=NOINLINE] :: Eval3.Eval ()
[GblId, Str=DmdType]
OptimizeMonadTrans.example =
  a10_rTz
  `cast` (Sym <(Eval3.NTCo:Eval <()>)>
          :: (Eval3.Value -> Eval3.Value -> GHC.Types.IO ())
               ~#
             Eval3.Eval ())

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
  \ (s_ajB :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    case GHC.Prim.newMutVar#
           @ GHC.Types.Int @ GHC.Prim.RealWorld Eval3.runEval2 s_ajB
    of _ { (# ipv_ajS, ipv1_ajT #) ->
    let {
      a11_sk0 :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
      [LclId, Str=DmdType m]
      a11_sk0 =
        GHC.STRef.STRef @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_ajT } in
    case (((OptimizeMonadTrans.example
            `cast` (<Eval3.NTCo:Eval <()>>
                    :: Eval3.Eval ()
                         ~#
                       (Eval3.Value -> Eval3.Value -> GHC.Types.IO ())))
             (a11_sk0
              `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int>
                      :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                           ~#
                         GHC.IORef.IORef GHC.Types.Int))
             (a11_sk0
              `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int>
                      :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                           ~#
                         GHC.IORef.IORef GHC.Types.Int)))
          `cast` (<GHC.Types.NTCo:IO <()>>
                  :: GHC.Types.IO ()
                       ~#
                     (GHC.Prim.State# GHC.Prim.RealWorld
                      -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #))))
           ipv_ajS
    of _ { (# ipv2_XkI, _ #) ->
    case GHC.Prim.readMutVar#
           @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_ajT ipv2_XkI
    of _ { (# ipv4_ajE, ipv5_ajF #) ->
    GHC.IO.Handle.Text.hPutStr2
      GHC.IO.Handle.FD.stdout
      (GHC.Show.$fShowInt_$cshow ipv5_ajF)
      GHC.Types.True
      ipv4_ajE
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



