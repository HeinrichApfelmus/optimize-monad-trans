PHONY: core

OBJ=build
COMPILE=ghc --make -outputdir $(OBJ) -i$(OBJ) -L$(OBJ)
GHC_OPTS=-O -ddump-simpl -dsuppress-coercions -dsuppress-uniques

# Compile and inspect core for the inner loop
MODULE=OptimizeMonadTrans

core1 :
	$(COMPILE) -DEVAL=Eval1 -fforce-recomp \
		$(GHC_OPTS) \
		$(MODULE).hs > results/$(MODULE).core1.hs

core2 :
	$(COMPILE) -DEVAL=Eval2 -fforce-recomp \
		$(GHC_OPTS) \
		$(MODULE).hs > results/$(MODULE).core2.hs

core3 :
	$(COMPILE) -DEVAL=Eval3 -fforce-recomp \
		$(GHC_OPTSｓ) \
		$(MODULE).hs > results/$(MODULE).core3.hs

core3s :
	$(COMPILE) -DEVAL=Eval3 -DSHARING -fforce-recomp \
		$(GHC_OPTS) \
		$(MODULE).hs > results/$(MODULE).core3s.hs

coreImplicit :
	$(COMPILE) -DEVAL=Eval1 -DIMPLICIT -fforce-recomp \
		$(GHC_OPTS) \
		$(MODULE).hs > results/$(MODULE).coreImplicit.hs

coreRefl :
	$(COMPILE) -DEVAL=Eval1 -DREFLECTION -fforce-recomp \
		$(GHC_OPTS) \
		$(MODULE).hs > results/$(MODULE).coreRefl.hs
