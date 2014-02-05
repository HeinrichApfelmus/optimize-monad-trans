[1 of 2] Compiling Eval3            ( Eval3.hs, build/Eval3.o )

==================== Tidy Core ====================
Result size of Tidy Core = {terms: 129, types: 232, coercions: 162}

Eval3.run1 :: forall a_g. Eval3.Eval a_g -> Eval3.Eval a_g
[GblId,
 Arity=1,
 Caf=NoCafRefs,
 Str=DmdType S,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=1, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval3.run1 = \ (@ a_g) (ds_dhR :: Eval3.Eval a_g) -> ds_dhR

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
  :: forall a_ahf. GHC.Types.IO a_ahf -> Eval3.Eval a_ahf
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
                 (s_ajk [Occ=Once] :: GHC.Prim.State# GHC.Prim.RealWorld) ->
                 (# s_ajk, x_afJ #)}]
Eval3.ask3 =
  \ (x_afJ :: Eval3.Value)
    _
    (s_ajk :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# s_ajk, x_afJ #)

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
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, b_tD #)
[GblId,
 Arity=5,
 Caf=NoCafRefs,
 Str=DmdType C(C(C(U(LL))))LLLL,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=5, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval3.$fMonadEval2 =
  \ (@ a_tC)
    (@ b_tD)
    (m_afP :: Eval3.Eval a_tC)
    (k_afQ :: a_tC -> Eval3.Eval b_tD)
    (x_afR :: Eval3.Value)
    (y_afS :: Eval3.Value)
    (s_ajv :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    case (((m_afP
            `cast` (<Eval3.NTCo:Eval <a_tC>>
                    :: Eval3.Eval a_tC
                         ~#
                       (Eval3.Value -> Eval3.Value -> GHC.Types.IO a_tC)))
             x_afR y_afS)
          `cast` (<GHC.Types.NTCo:IO <a_tC>>
                  :: GHC.Types.IO a_tC
                       ~#
                     (GHC.Prim.State# GHC.Prim.RealWorld
                      -> (# GHC.Prim.State# GHC.Prim.RealWorld, a_tC #))))
           s_ajv
    of _ { (# ipv_ajy, ipv1_ajz #) ->
    ((((k_afQ ipv1_ajz)
       `cast` (<Eval3.NTCo:Eval <b_tD>>
               :: Eval3.Eval b_tD
                    ~#
                  (Eval3.Value -> Eval3.Value -> GHC.Types.IO b_tD)))
        x_afR y_afS)
     `cast` (<GHC.Types.NTCo:IO <b_tD>>
             :: GHC.Types.IO b_tD
                  ~#
                (GHC.Prim.State# GHC.Prim.RealWorld
                 -> (# GHC.Prim.State# GHC.Prim.RealWorld, b_tD #))))
      ipv_ajy
    }

Eval3.$fMonadEval_$c>>=
  :: forall a_agd b_age.
     Eval3.Eval a_agd -> (a_agd -> Eval3.Eval b_age) -> Eval3.Eval b_age
[GblId,
 Arity=5,
 Caf=NoCafRefs,
 Str=DmdType C(C(C(U(LL))))LLLL,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval3.$fMonadEval_$c>>= =
  Eval3.$fMonadEval2
  `cast` (forall a_tC b_tD.
          <Eval3.Eval a_tC>
          -> <a_tC -> Eval3.Eval b_tD>
          -> (<Eval3.Value>
              -> <Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <b_tD>)>) ; Sym
                                                                        <(Eval3.NTCo:Eval <b_tD>)>
          :: (forall a_tC b_tD.
              Eval3.Eval a_tC
              -> (a_tC -> Eval3.Eval b_tD)
              -> Eval3.Value
              -> Eval3.Value
              -> GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, b_tD #))
               ~#
             (forall a_tC b_tD.
              Eval3.Eval a_tC -> (a_tC -> Eval3.Eval b_tD) -> Eval3.Eval b_tD))

Eval3.$fMonadEval1
  :: forall a_tM.
     a_tM
     -> Eval3.Value
     -> Eval3.Value
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, a_tM #)
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType LAAL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=4, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ a_tM)
                 (a1_afO [Occ=Once] :: a_tM)
                 _
                 _
                 (eta2_B1 [Occ=Once] :: GHC.Prim.State# GHC.Prim.RealWorld) ->
                 (# eta2_B1, a1_afO #)}]
Eval3.$fMonadEval1 =
  \ (@ a_tM)
    (a1_afO :: a_tM)
    _
    _
    (eta2_B1 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# eta2_B1, a1_afO #)

Eval3.$fMonadEval_$creturn
  :: forall a_ah4. a_ah4 -> Eval3.Eval a_ah4
[GblId,
 Arity=4,
 Caf=NoCafRefs,
 Str=DmdType LAAL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Eval3.$fMonadEval1
               `cast` (forall a_tM.
                       <a_tM>
                       -> (<Eval3.Value>
                           -> <Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <a_tM>)>) ; Sym
                                                                                     <(Eval3.NTCo:Eval
                                                                                         <a_tM>)>
                       :: (forall a_tM.
                           a_tM
                           -> Eval3.Value
                           -> Eval3.Value
                           -> GHC.Prim.State# GHC.Prim.RealWorld
                           -> (# GHC.Prim.State# GHC.Prim.RealWorld, a_tM #))
                            ~#
                          (forall a_tM. a_tM -> Eval3.Eval a_tM))}]
Eval3.$fMonadEval_$creturn =
  Eval3.$fMonadEval1
  `cast` (forall a_tM.
          <a_tM>
          -> (<Eval3.Value>
              -> <Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <a_tM>)>) ; Sym
                                                                        <(Eval3.NTCo:Eval <a_tM>)>
          :: (forall a_tM.
              a_tM
              -> Eval3.Value
              -> Eval3.Value
              -> GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, a_tM #))
               ~#
             (forall a_tM. a_tM -> Eval3.Eval a_tM))

Eval3.$fMonadEval_$cfail
  :: forall a_ahD. GHC.Base.String -> Eval3.Eval a_ahD
[GblId, Arity=1, Str=DmdType Sb]
Eval3.$fMonadEval_$cfail =
  \ (@ a_ain) (eta_B1 :: [GHC.Types.Char]) ->
    GHC.Err.error @ (Eval3.Eval a_ain) eta_B1

a_rkV
  :: forall a_agX b_agY.
     Eval3.Eval a_agX
     -> Eval3.Eval b_agY
     -> Eval3.Value
     -> Eval3.Value
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, b_agY #)
[GblId, Arity=5, Caf=NoCafRefs, Str=DmdType C(C(C(U(LA))))LLLL]
a_rkV =
  \ (@ a_agX)
    (@ b_agY)
    (eta_B2 :: Eval3.Eval a_agX)
    (eta1_B1 :: Eval3.Eval b_agY)
    (eta2_B3 :: Eval3.Value)
    (eta3_X4 :: Eval3.Value)
    (eta4_X7 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    case (((eta_B2
            `cast` (<Eval3.NTCo:Eval <a_agX>>
                    :: Eval3.Eval a_agX
                         ~#
                       (Eval3.Value -> Eval3.Value -> GHC.Types.IO a_agX)))
             eta2_B3 eta3_X4)
          `cast` (<GHC.Types.NTCo:IO <a_agX>>
                  :: GHC.Types.IO a_agX
                       ~#
                     (GHC.Prim.State# GHC.Prim.RealWorld
                      -> (# GHC.Prim.State# GHC.Prim.RealWorld, a_agX #))))
           eta4_X7
    of _ { (# ipv_ajy, _ #) ->
    (((eta1_B1
       `cast` (<Eval3.NTCo:Eval <b_agY>>
               :: Eval3.Eval b_agY
                    ~#
                  (Eval3.Value -> Eval3.Value -> GHC.Types.IO b_agY)))
        eta2_B3 eta3_X4)
     `cast` (<GHC.Types.NTCo:IO <b_agY>>
             :: GHC.Types.IO b_agY
                  ~#
                (GHC.Prim.State# GHC.Prim.RealWorld
                 -> (# GHC.Prim.State# GHC.Prim.RealWorld, b_agY #))))
      ipv_ajy
    }

Eval3.$fMonadEval_$c>> [InlPrag=INLINE (sat-args=2)]
  :: forall a_agX b_agY.
     Eval3.Eval a_agX -> Eval3.Eval b_agY -> Eval3.Eval b_agY
[GblId,
 Arity=5,
 Caf=NoCafRefs,
 Str=DmdType C(C(C(U(LA))))LLLL,
 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=2, Value=True,
         ConLike=True, WorkFree=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=False,boring_ok=False)
         Tmpl= \ (@ a_aig)
                 (@ b_aih)
                 (m_aii [Occ=Once] :: Eval3.Eval a_aig)
                 (k_aij [Occ=OnceL] :: Eval3.Eval b_aih) ->
                 Eval3.$fMonadEval_$c>>= @ a_aig @ b_aih m_aii (\ _ -> k_aij)}]
Eval3.$fMonadEval_$c>> =
  a_rkV
  `cast` (forall a_agX b_agY.
          <Eval3.Eval a_agX>
          -> <Eval3.Eval b_agY>
          -> (<Eval3.Value>
              -> <Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <b_agY>)>) ; Sym
                                                                         <(Eval3.NTCo:Eval <b_agY>)>
          :: (forall a_agX b_agY.
              Eval3.Eval a_agX
              -> Eval3.Eval b_agY
              -> Eval3.Value
              -> Eval3.Value
              -> GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, b_agY #))
               ~#
             (forall a_agX b_agY.
              Eval3.Eval a_agX -> Eval3.Eval b_agY -> Eval3.Eval b_agY))

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
             -> <a_X1l -> Eval3.Eval b_X1n>
             -> (<Eval3.Value>
                 -> <Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <b_X1n>)>) ; Sym
                                                                            <(Eval3.NTCo:Eval
                                                                                <b_X1n>)>
             :: (forall a_X1l b_X1n.
                 Eval3.Eval a_X1l
                 -> (a_X1l -> Eval3.Eval b_X1n)
                 -> Eval3.Value
                 -> Eval3.Value
                 -> GHC.Prim.State# GHC.Prim.RealWorld
                 -> (# GHC.Prim.State# GHC.Prim.RealWorld, b_X1n #))
                  ~#
                (forall a_X1l b_X1n.
                 Eval3.Eval a_X1l
                 -> (a_X1l -> Eval3.Eval b_X1n) -> Eval3.Eval b_X1n)))
    Eval3.$fMonadEval_$c>>
    (Eval3.$fMonadEval1
     `cast` (forall a_X1o.
             <a_X1o>
             -> (<Eval3.Value>
                 -> <Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <a_X1o>)>) ; Sym
                                                                            <(Eval3.NTCo:Eval
                                                                                <a_X1o>)>
             :: (forall a_X1o.
                 a_X1o
                 -> Eval3.Value
                 -> Eval3.Value
                 -> GHC.Prim.State# GHC.Prim.RealWorld
                 -> (# GHC.Prim.State# GHC.Prim.RealWorld, a_X1o #))
                  ~#
                (forall a_X1o. a_X1o -> Eval3.Eval a_X1o)))
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
    of _ { (# ipv_ajM, ipv1_ajN #) ->
    let {
      a1_sjU :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
      [LclId, Str=DmdType m]
      a1_sjU =
        GHC.STRef.STRef @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_ajN } in
    case (((m_afL
            `cast` (<Eval3.NTCo:Eval <void_m>>
                    :: Eval3.Eval void_m
                         ~#
                       (Eval3.Value -> Eval3.Value -> GHC.Types.IO void_m)))
             (a1_sjU
              `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int>
                      :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                           ~#
                         GHC.IORef.IORef GHC.Types.Int))
             (a1_sjU
              `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int>
                      :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                           ~#
                         GHC.IORef.IORef GHC.Types.Int)))
          `cast` (<GHC.Types.NTCo:IO <void_m>>
                  :: GHC.Types.IO void_m
                       ~#
                     (GHC.Prim.State# GHC.Prim.RealWorld
                      -> (# GHC.Prim.State# GHC.Prim.RealWorld, void_m #))))
           ipv_ajM
    of _ { (# ipv2_XkC, _ #) ->
    GHC.Prim.readMutVar#
      @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_ajN ipv2_XkC
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
                 (s_ajk [Occ=Once] :: GHC.Prim.State# GHC.Prim.RealWorld) ->
                 (# s_ajk, y_afK #)}]
Eval3.ask4 =
  \ _
    (y_afK :: Eval3.Value)
    (s_ajk :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# s_ajk, y_afK #)

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
Result size of Tidy Core = {terms: 159, types: 183, coercions: 60}

a_rSn :: GHC.Types.Int
[GblId, Caf=NoCafRefs, Str=DmdType m]
a_rSn = GHC.Types.I# 1

a1_rSo
  :: Eval3.Value
     -> Eval3.Value
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #)
[GblId, Arity=3, Caf=NoCafRefs, Str=DmdType AAL]
a1_rSo =
  \ _ _ (eta2_X1b :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# eta2_X1b, a_rSn #)

a2_rSp :: GHC.Types.Int
[GblId, Caf=NoCafRefs, Str=DmdType m]
a2_rSp = GHC.Types.I# 2

a3_rSq
  :: Eval3.Value
     -> Eval3.Value
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #)
[GblId, Arity=3, Caf=NoCafRefs, Str=DmdType AAL]
a3_rSq =
  \ _ _ (eta2_X1v :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    (# eta2_X1v, a2_rSp #)

a4_rSr :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a4_rSr =
  GHC.Types.:
    @ OptimizeMonadTrans.Tree
    OptimizeMonadTrans.Leaf
    (GHC.Types.[] @ OptimizeMonadTrans.Tree)

a5_rSs :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a5_rSs =
  GHC.Types.:
    @ OptimizeMonadTrans.Tree OptimizeMonadTrans.Leaf a4_rSr

a6_rSt :: OptimizeMonadTrans.Tree
[GblId, Caf=NoCafRefs, Str=DmdType]
a6_rSt =
  OptimizeMonadTrans.Branch
    (a3_rSq
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
    a5_rSs

a7_rSu :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a7_rSu = GHC.Types.: @ OptimizeMonadTrans.Tree a6_rSt a4_rSr

tree_rq7 :: OptimizeMonadTrans.Tree
[GblId, Caf=NoCafRefs, Str=DmdType]
tree_rq7 =
  OptimizeMonadTrans.Branch
    (a1_rSo
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
    a7_rSu

Rec {
a8_rSv
  :: [OptimizeMonadTrans.Tree]
     -> Eval3.Value
     -> Eval3.Value
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #)
[GblId, Arity=4, Caf=NoCafRefs, Str=DmdType SLLL]
a8_rSv =
  \ (ds_dzi :: [OptimizeMonadTrans.Tree])
    (eta_B3 :: Eval3.Value)
    (eta1_B2 :: Eval3.Value)
    (eta2_B1 :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    case ds_dzi of _ {
      [] -> (# eta2_B1, GHC.Tuple.() #);
      : x_atD xs_atE ->
        case x_atD of _ {
          OptimizeMonadTrans.Branch action_atG children_atH ->
            case (((action_atG
                    `cast` (<Eval3.NTCo:Eval <GHC.Types.Int>>
                            :: Eval3.Eval GHC.Types.Int
                                 ~#
                               (Eval3.Value -> Eval3.Value -> GHC.Types.IO GHC.Types.Int)))
                     eta_B3 eta1_B2)
                  `cast` (<GHC.Types.NTCo:IO <GHC.Types.Int>>
                          :: GHC.Types.IO GHC.Types.Int
                               ~#
                             (GHC.Prim.State# GHC.Prim.RealWorld
                              -> (# GHC.Prim.State# GHC.Prim.RealWorld, GHC.Types.Int #))))
                   eta2_B1
            of _ { (# ipv_ajy, ipv1_ajz #) ->
            case eta_B3
                 `cast` (<GHC.IORef.NTCo:IORef> <GHC.Types.Int>
                         :: GHC.IORef.IORef GHC.Types.Int
                              ~#
                            GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int)
            of wild2_ajZ { GHC.STRef.STRef var#_ak1 ->
            case GHC.Prim.readMutVar#
                   @ GHC.Prim.RealWorld @ GHC.Types.Int var#_ak1 ipv_ajy
            of _ { (# ipv2_Xkt, ipv3_Xkv #) ->
            case ipv1_ajz of _ { GHC.Types.I# x1_aAN ->
            case ipv3_Xkv of _ { GHC.Types.I# y_aAR ->
            case GHC.Prim.writeMutVar#
                   @ GHC.Prim.RealWorld
                   @ GHC.Types.Int
                   var#_ak1
                   (GHC.Types.I# (GHC.Prim.+# x1_aAN y_aAR))
                   ipv2_Xkt
            of s2#_aCc { __DEFAULT ->
            a8_rSv
              (GHC.Base.++ @ OptimizeMonadTrans.Tree children_atH xs_atE)
              (wild2_ajZ
               `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int>
                       :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                            ~#
                          GHC.IORef.IORef GHC.Types.Int))
              eta1_B2
              s2#_aCc
            }
            }
            }
            }
            }
            };
          OptimizeMonadTrans.Leaf ->
            case eta1_B2
                 `cast` (<GHC.IORef.NTCo:IORef> <GHC.Types.Int>
                         :: GHC.IORef.IORef GHC.Types.Int
                              ~#
                            GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int)
            of wild2_ajZ { GHC.STRef.STRef var#_ak1 ->
            case GHC.Prim.readMutVar#
                   @ GHC.Prim.RealWorld @ GHC.Types.Int var#_ak1 eta2_B1
            of _ { (# ipv_Xk1, ipv1_Xk3 #) ->
            case ipv1_Xk3 of _ { GHC.Types.I# x1_aAN ->
            case GHC.Prim.writeMutVar#
                   @ GHC.Prim.RealWorld
                   @ GHC.Types.Int
                   var#_ak1
                   (GHC.Types.I# (GHC.Prim.+# x1_aAN 1))
                   ipv_Xk1
            of s2#_aCc { __DEFAULT ->
            a8_rSv
              xs_atE
              eta_B3
              (wild2_ajZ
               `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int>
                       :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                            ~#
                          GHC.IORef.IORef GHC.Types.Int))
              s2#_aCc
            }
            }
            }
            }
        }
    }
end Rec }

a9_rSw :: [OptimizeMonadTrans.Tree]
[GblId, Caf=NoCafRefs, Str=DmdType]
a9_rSw =
  GHC.Types.:
    @ OptimizeMonadTrans.Tree
    tree_rq7
    (GHC.Types.[] @ OptimizeMonadTrans.Tree)

a10_rSx
  :: Eval3.Value
     -> Eval3.Value
     -> GHC.Prim.State# GHC.Prim.RealWorld
     -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #)
[GblId, Arity=3, Str=DmdType]
a10_rSx = a8_rSv a9_rSw

OptimizeMonadTrans.example [InlPrag=NOINLINE] :: Eval3.Eval ()
[GblId, Str=DmdType]
OptimizeMonadTrans.example =
  a10_rSx
  `cast` ((<Eval3.Value>
           -> <Eval3.Value> -> Sym <(GHC.Types.NTCo:IO <()>)>) ; Sym
                                                                   <(Eval3.NTCo:Eval <()>)>
          :: (Eval3.Value
              -> Eval3.Value
              -> GHC.Prim.State# GHC.Prim.RealWorld
              -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #))
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
  \ (s_Xkw :: GHC.Prim.State# GHC.Prim.RealWorld) ->
    case GHC.Prim.newMutVar#
           @ GHC.Types.Int @ GHC.Prim.RealWorld Eval3.runEval2 s_Xkw
    of _ { (# ipv_ajM, ipv1_ajN #) ->
    let {
      a11_sjU :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
      [LclId, Str=DmdType m]
      a11_sjU =
        GHC.STRef.STRef @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_ajN } in
    case (((OptimizeMonadTrans.example
            `cast` (<Eval3.NTCo:Eval <()>>
                    :: Eval3.Eval ()
                         ~#
                       (Eval3.Value -> Eval3.Value -> GHC.Types.IO ())))
             (a11_sjU
              `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int>
                      :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                           ~#
                         GHC.IORef.IORef GHC.Types.Int))
             (a11_sjU
              `cast` (Sym <(GHC.IORef.NTCo:IORef)> <GHC.Types.Int>
                      :: GHC.STRef.STRef GHC.Prim.RealWorld GHC.Types.Int
                           ~#
                         GHC.IORef.IORef GHC.Types.Int)))
          `cast` (<GHC.Types.NTCo:IO <()>>
                  :: GHC.Types.IO ()
                       ~#
                     (GHC.Prim.State# GHC.Prim.RealWorld
                      -> (# GHC.Prim.State# GHC.Prim.RealWorld, () #))))
           ipv_ajM
    of _ { (# ipv2_XkC, _ #) ->
    case GHC.Prim.readMutVar#
           @ GHC.Prim.RealWorld @ GHC.Types.Int ipv1_ajN ipv2_XkC
    of _ { (# ipv4_ajy, ipv5_ajz #) ->
    GHC.IO.Handle.Text.hPutStr2
      GHC.IO.Handle.FD.stdout
      (GHC.Show.$fShowInt_$cshow ipv5_ajz)
      GHC.Types.True
      ipv4_ajy
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



