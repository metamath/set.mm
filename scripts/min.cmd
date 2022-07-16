! min.cmd
! Creates a script 1.tmp to "minimize" multiple proofs.  The list of proofs
! to minimize should be a set of lines stored in a file called 1.tmp.  Each
! line should start with at least 2 spaces (otherwise it will be ignored)
! and have space-separated labels on each line, e.g.:
!
! "  mp2b mp1i mpbid"
! "  mpii"
!
! The output of commands such as "show usage", when logged into 1.tmp, will
! have the correct format.
!
! Before running 1.tmp as a script from MM>, change "xxx" in 1.tmp to the
! label list (such as "ax-?,mp*") to scan to see if the proof size is
! reduced.
!
! Example: we want to see if any theorem currently using "funsn1" or
! "funsn2" can be "minimize"d with 2 newly added theorems "fnsn1" and
! "fnsn2" within "set.mm":
!
! MM> read set.mm
! MM> open log 1.tmp
! MM> show usage funsn1,funsn2
! MM> close log
! MM> submit "scripts/min.cmd"
! MM> tools
! TOOLS> substitute 1.tmp xxx fnsn1,fnsn2 a ""
! TOOLS> exit
! MM> open log log.txt                (recommended, to review result later)
! MM> submit 1.tmp
! MM> write source set.mm /rewrap
! MM> close log

tools
match 1.tmp '(None)' n
match 1.tmp 'MM>' n
match 1.tmp '  ' y
break 1.tmp ''
unduplicate 1.tmp
add 1.tmp 'prove ' '$min xxx/allow */no_new ax-*$save new_proof/compressed$_exit_pa$'
! If you want to do a "dry run" without saving proofs, change above line
! to:
! add 1.tmp 'prove ' '$min xxx/no_new ax-*$_exit_pa/force$'
substitute 1.tmp '$' '\n' a ''
quit
