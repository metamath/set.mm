# Makefile to minimize Metamath proofs. Requires GNU make.
# "work" is a space-separated list of simple numbers.

all: alljobs
	@echo 'Completion time:'
	@date
	@echo
	@echo 'DONE.'
.PHONY: all

MMFILE ?= set.mm
JOBSDIR ?= metamathjobs

DONE_LIST := \
  $(foreach num, $(work), $(JOBSDIR)/job$(num).done)

$(JOBSDIR)/job%.done: $(JOBSDIR)/job%.cmd
	@echo 'Running job $(*)'
	@rm -f '$(JOBSDIR)/job$(*).log'
	time metamath 'read $(MMFILE)' \
	  "open log '$(JOBSDIR)/job$(*).log'" \
	  "submit '$(JOBSDIR)/job$(*).cmd' /silent" quit 2>&1
	@echo 'Completed job $(*)'
	@touch '$(JOBSDIR)/job$(*).done'

alljobs: $(DONE_LIST)
.PHONY: alljobs

# Delete what we're creating on error.
# NOTE: We do *NOT* delete partial logs, since they are not make targets.
# Keeping logs around simplifies debugging.
.DELETE_ON_ERROR:

$(info Began running make on:)
$(info $(shell date))
