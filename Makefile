PHONY: core

OBJ=build
COMPILE=ghc --make -outputdir $(OBJ) -i$(OBJ) -L$(OBJ)

# Compile and inspect core for the inner loop
MODULE=OptimizeMonadTrans

core1 :
	$(COMPILE) -DEVAL=Eval1 -fforce-recomp \
		-O -ddump-simpl \
		$(MODULE).hs > results/$(MODULE).core1.hs

core2 :
	$(COMPILE) -DEVAL=Eval2 -fforce-recomp \
		-O -ddump-simpl \
		$(MODULE).hs > results/$(MODULE).core2.hs

core3 :
	$(COMPILE) -DEVAL=Eval3 -fforce-recomp \
		-O -ddump-simpl \
		$(MODULE).hs > results/$(MODULE).core3.hs

core3s :
	$(COMPILE) -DEVAL=Eval3 -DSHARING -fforce-recomp \
		-O -ddump-simpl \
		$(MODULE).hs > results/$(MODULE).core3s.hs

coreImplicit :
	$(COMPILE) -DEVAL=Eval1 -DIMPLICIT -fforce-recomp \
		-O -ddump-simpl \
		$(MODULE).hs > results/$(MODULE).coreImplicit.hs

coreRefl :
	$(COMPILE) -DEVAL=Eval1 -DREFLECTION -fforce-recomp \
		-O -ddump-simpl \
		$(MODULE).hs > results/$(MODULE).coreRefl.hs
