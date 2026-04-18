include config.mk

CC 				= cc
LIBS 			= ${RUNARA_LIBS} ${PLATFORM_SPECIFIC_LIBS} $(shell pkg-config --libs freetype2 harfbuzz)
CFLAGS		= ${WINDOWING} ${ADDITIONAL_FLAGS} -Wall -pedantic -O3 -ffast-math -g $(shell pkg-config --cflags freetype2 harfbuzz)
SRC_FILES = $(wildcard src/*.c src/widgets/*.c) $(PLATFORM_SPECIFIC)
OBJ_FILES = $(SRC_FILES:.c=.o)

all: lib/libleif.a

lib/libleif.a: $(OBJ_FILES)
	mkdir -p lib
	ar cr lib/libleif.a $(OBJ_FILES)
	rm -f $(OBJ_FILES)

%.o: %.c
	${CC} -c $< -o $@ ${LIBS} ${CFLAGS}

lib:
	mkdir -p lib

clean:
	rm -rf lib

install:
	cp lib/libleif.a /usr/local/lib/ 
	cp -r include/leif /usr/local/include/ 

uninstall:
	rm -f /usr/local/lib/libleif.a
	rm -rf /usr/local/include/leif/

.PHONY: all clean install uninstall
