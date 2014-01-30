PHONY: core

OBJ=build
COMPILE=ghc --make -outputdir $(OBJ) -i$(OBJ) -L$(OBJ)

# Compile and inspect core for the inner loop
MODULE=OptimizeMonadTrans

core1 :
	$(COMPILE) -DVARIANT1 -fforce-recomp -O -ddump-simpl \
		$(MODULE).hs > $(MODULE).core1.hs

core2 :
	$(COMPILE) -DVARIANT2 -fforce-recomp -O -ddump-simpl \
		$(MODULE).hs > $(MODULE).core2.hs