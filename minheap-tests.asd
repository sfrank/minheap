(in-package :common-lisp-user)

(asdf:defsystem :minheap-tests
  :description "Various heap/priority queue data structures; the tests"
  :maintainer "Stephan Frank <defclass@googlemail.com>"
  :license "BSD, see LICENSE"
  :depends-on (:lisp-unit :minheap)
  :components ((:module test
                :components ((:file "binary-heap-test")
                             (:file "fib-heap-test")
                             (:file "pairing-heap-elmasri-test")
                             (:file "pairing-heap-test")
                             (:file "rank-pairing-heap-test")
                             (:file "rank-pairing-heap-clist-test")
                             (:file "violation-heap-test")))))