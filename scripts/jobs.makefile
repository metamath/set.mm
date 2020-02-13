# Makefile to minimize Metamath proofs. Requires GNU make.
# "work" is a list of simple numbers.

all: alljobs
	@echo 'DONE.'

LOG_LIST := \
  $(foreach num, $(work), metamathjobs/job$(num).log)

metamathjobs/job%.log: metamathjobs/job%.cmd
	@echo "Running job $*"
	@rm -f "metamathjobs/job$(*).log"
	time metamath 'read set.mm' \
	  "open log 'metamathjobs/job$(*).log'" \
	  "submit 'metamathjobs/job$(*).cmd' /silent" quit 2>&1

alljobs: $(LOG_LIST)

# Delete what's generated if a program returns a nonzero (error) result.
# This can be annoying for debugging, but it means that we can simply re-run
# make if a process is stopped.
ifndef KEEP_ON_ERROR
.DELETE_ON_ERROR:
endif
