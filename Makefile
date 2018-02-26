CC      = gcc
CFLAGS  = -Wall -g -DDATA_ORDER_IS_BIG_ENDIAN
EXECS   = main

.SUFFIXES: .o .c

all: $(EXECS)

launcher: $(MOBJS)
	$(CC) $(CFLAGS) -o $@ $(MOBJS) $(LFLAGS)

.c.o: %.c
	$(CC) $(CFLAGS) -c $*.c

clean:
	 /bin/rm -f *.o *~ $(EXECS)

