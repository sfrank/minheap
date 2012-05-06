(in-package :common-lisp-user)

(asdf:defsystem :minheap
  :description "Various heap/priority queue data structures"
  :maintainer "Stephan Frank <defclass@googlemail.com>"
  :license "BSD, see LICENSE"
  :components
  ((:file "binary-heap")
   (:file "fib-heap")
   (:file "pairing-heap-elmasri")
   (:file "pairing-heap")
   (:file "pairing-heap-listbased")
   (:file "rank-pairing-heap")
   (:file "rank-pairing-heap-clist")
   (:file "splay-heap")
   (:file "violation-heap")))
