TARGET = sscmhist.exe
LIBS = sscmapi.lib
CC = cl
INLCUDE_PATH = "C:\Progs\Perforce\Surround SCM\API\include"
LIB_PATH = "C:\Progs\Perforce\Surround SCM\API\lib"

all: sscmhist

sscmhist:
	$(CC) /Fe:$(TARGET) /I $(INLCUDE_PATH) sscmhist.c $(LIBS) /link /LIBPATH:$(LIB_PATH)
