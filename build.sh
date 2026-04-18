mkdir -p bin
gcc -o bin/terminator terminator.c \
$(pkg-config --cflags freetype2 harfbuzz) \
-lleif -lrunara \
$(pkg-config --libs freetype2 harfbuzz) \
-lm -lGL -lX11 -lXrender -lXrandr -lXinerama -lXcursor -lfontconfig