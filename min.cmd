! min.cmd
! Creates a script to "minimize" multiple proofs.  The list of proofs to
! minimize should be a set of lines stored in a file called 1.tmp.  Each
! line should start with 2 spaces (otherwise it will be ignored) and have
! space-separated labels on each line, e.g.:
!
! "  mp2b mp1i mpbid"
! "  mpii"
!
! The output of commands such as "show usage", when logged into 1.tmp,
! will have the correct format.
!
! Before running 1.tmp as a script from MM>, change "xxx" in 1.tmp to
! the label list (such as "ax-?,mp*") to scan to see if the proof size
! is reduced.

! Example: we want to see if any theorem currently using "funsn" can
! be "minimize"d with 2 newly added theorems "fnsn1" and "fnsn2".
!
! MM> open log 1.tmp
! MM> show usage funsn
! MM> close log
! MM> submit min.cmd
! MM> tools
! MM> substitute 1.tmp xxx fnsn1,fnsn2 a ""
! MM> exit
! MM> open log log.txt                   (recommended, to review result later)
! MM> submit 1.tmp
! MM> close log

tools
match 1.tmp '(None)' n
match 1.tmp 'MM>' n
match 1.tmp '  ' y
break 1.tmp ''
add 1.tmp 'prove ' '$min xxx/no_new ax-*$save new_proof/compressed$_exit_pa$'
substitute 1.tmp '$' '\n' a ''
quit
