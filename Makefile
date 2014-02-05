PHONY: core

OBJ=build
COMPILE=ghc --make -outputdir $(OBJ) -i$(OBJ) -L$(OBJ)

# Compile and inspect core for the inner loop
MODULE=OptimizeMonadTrans

core1 :
	$(COMPILE) -DEVAL=Eval1 -fforce-recomp \
		-O -ddump-simpl \
		$(MODULE).hs > $(MODULE).core1.hs

core2 :
	$(COMPILE) -DEVAL=Eval2 -fforce-recomp \
		-O -ddump-simpl \
		$(MODULE).hs > $(MODULE).core2.hs

core3 :
	$(COMPILE) -DEVAL=Eval3 -fforce-recomp \
		-O -ddump-simpl \
		$(MODULE).hs > $(MODULE).core3.hs

core3s :
	$(COMPILE) -DEVAL=Eval3 -DSHARING -fforce-recomp \
		-O -ddump-simpl \
		$(MODULE).hs > $(MODULE).core3s.hs

coreImplicit :
	$(COMPILE) -DEVAL=Eval1 -DIMPLICIT -fforce-recomp \
		-O -ddump-simpl \
		$(MODULE).hs > $(MODULE).coreImplicit.hs

coreRefl :
	$(COMPILE) -DEVAL=Eval1 -DREFLECTION -fforce-recomp \
		-O -ddump-simpl \
		$(MODULE).hs > $(MODULE).coreRefl.hs
