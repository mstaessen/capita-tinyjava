CC      = gcc
CCFLAGS = -c -pthread 
LD      = gcc
LDFLAGS = 

JAVAC   = javac

VF      = /path/to/verifast

MKDIR   = mkdir
MDFLAGS = -p
MV      = mv
CP      = cp
RM      = rm
RMFLAGS = -rf

main: tinyjava
	
tinyjava: init tmp/chars_reader.o tmp/threading.o tmp/util.o tmp/tinyjava.o
	$(LD) $(LDFLAGS) tmp/*.o -o bin/tinyjava
	
init: 
	$(MKDIR) $(MDFLAGS) tmp bin
	
tmp/%.o: src/%.c
	@echo "Compiling $@..."
	$(CC) $(CCFLAGS) -o $@ $<
	
examples: tinyjava
	@echo "Compiling example files..."
	$(JAVAC) -d bin examples/*.java
	
test: tinyjava
	$(VF) listex.obj arrays.obj chars reader.obj threading.obj util.obj src/tinyjava.c
    
clean:
	$(RM) $(RMFLAGS) tmp bin