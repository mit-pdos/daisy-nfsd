# dafny-jrnl

goose-nfsd has a verified journal. We write verified code against that journal.
Using the specification of the journal, the overall system makes every
operation atomic with respect to both concurrency and crashes.
