# Makefile to minimize Metamath proofs. Requires GNU make.
# "work" is a space-separated list of simple numbers.

all: alljobs
	@echo 'Completion time:'
	@date
	@echo
	@echo 'DONE.'
.PHONY: all

MMFILE ?= set.mm

DONE_LIST := \
  $(foreach num, $(work), metamathjobs/job$(num).done)

metamathjobs/job%.done: metamathjobs/job%.cmd
	@echo 'Running job $(*)'
	@rm -f 'metamathjobs/job$(*).log'
	time metamath 'read $(MMFILE)' \
	  "open log 'metamathjobs/job$(*).log'" \
	  "submit 'metamathjobs/job$(*).cmd' /silent" quit 2>&1
	@echo 'Completed job $(*)'
	@touch 'metamathjobs/job$(*).done'

alljobs: $(DONE_LIST)
.PHONY: alljobs

# Delete what we're creating on error.
# NOTE: We do *NOT* delete partial logs, since they are not make targets.
# Keeping logs around simplifies debugging.
.DELETE_ON_ERROR:

$(info Began running make on:)
$(info $(shell date))
