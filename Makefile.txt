# Slope for PS2 - build with PS2SDK + gsKit (e.g. the ps2dev docker image)
EE_BIN  = slope.elf
EE_OBJS = main.o
EE_LIBS = -lgskit -ldmakit -lpad -lm

EE_INCS    += -I$(PS2DEV)/gsKit/include
EE_LDFLAGS += -L$(PS2DEV)/gsKit/lib

all: $(EE_BIN)

clean:
	rm -f $(EE_BIN) $(EE_OBJS)

include $(PS2SDK)/samples/Makefile.pref
include $(PS2SDK)/samples/Makefile.eeglobal
