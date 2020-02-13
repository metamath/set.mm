# Makefile to minimize Metamath proofs. Requires GNU make.

all: alljobs
	echo 'DONE.'

LOG_LIST := \
  $(foreach num, $(shell seq $(first) $(last)), metamathjobs/job$(num).log)

$(info LOG_LIST is $(LOG_LIST))

metamathjobs/job%.log: metamathjobs/job%.cmd
	echo "Running job $*"	
	metamath 'read set.mm' "submit 'metamathjobs/job$(*).cmd'" quit \
	   > "metamathjobs/job$(*).log" 2>&1

alljobs: $(LOG_LIST)

# Delete what's generated if a program returns a nonzero (error) result.
# This can be annoying for debugging, but it means that we can simply re-run
# make if a process is stopped.
ifndef KEEP_ON_ERROR
.DELETE_ON_ERROR:
endif
