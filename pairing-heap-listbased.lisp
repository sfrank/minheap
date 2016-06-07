;;;; MINHEAP is by Stephan Frank <defclass@googlemail.com>, 2007-2012.
;;;;
;;;; Permission is hereby granted, free of charge, to any person obtaining
;;;; a copy of this software and associated documentation files (the
;;;; "Software"), to deal in the Software without restriction, including
;;;; without limitation the rights to use, copy, modify, merge, publish,
;;;; distribute, sublicense, and/or sell copies of the Software, and to
;;;; permit persons to whom the Software is furnished to do so, subject to
;;;; the following conditions:
;;;;
;;;; The above copyright notice and this permission notice shall be included
;;;; in all copies or substantial portions of the Software.
;;;;
;;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;;;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;;;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;;;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;;;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

(defpackage :pairing-heap-list (:use :cl)
  (:export
   #:pairing-heap
   #:clear-heap
   #:empty-p
   #:insert
   #:peek-min
   #:extract-min
   #:extract-node
   #:heap-size
   #:decrease-key
   #:meld
   ))

(in-package :pairing-heap-list)

;;;; Variant of pairing-heap.lisp where the children of a node are
;;;; implemented as a list. The code is a lot more readable, however
;;;; due to the consing in attach-child this variant is about three
;;;; times slower than the more awkward implementation in
;;;; pairing-heap.lisp.

(defstruct (node (:constructor %make-node (key data)))
  (key 0 :type fixnum)
  (data nil)
  (children nil  :type list)
  (parent nil  :type (or null node)))

(defclass pairing-heap ()
  ((size :initform 0 :initarg :size
         :type (integer 0 *))
   (root :initform nil :initarg :root
         :type (or null node))))

(defmethod print-object ((obj pairing-heap) stream)
  (print-unreadable-object (obj stream :type t :identity t)
    (format stream "~4I~:_size: ~A~:_" (slot-value obj 'size))))

(declaim (inline heap-size))

(defun heap-size (heap)
  (slot-value heap 'size))

(defun empty-p (heap)
  (zerop (slot-value heap 'size)))

(defun clear-heap (heap)
  (setf (slot-value heap 'size) 0
        (slot-value heap 'root) nil)
  heap)

(defun peek-min (heap)
  (let ((node (slot-value heap 'root)))
    (assert node)
    (values (node-data node)
            (node-key node))))

(defun extract-min (heap)
  (let ((node (slot-value heap 'root)))
    (assert node)
    (setf (slot-value heap 'root) (combine-siblings node))
    (decf (slot-value heap 'size))
    (values (node-data node)
            (node-key node))))

(defun insert (heap key data)
  (let ((node (%make-node key data)))
    (incf (slot-value heap 'size))
    (setf (slot-value heap 'root)
          (if (slot-value heap 'root)
              (link (slot-value heap 'root) node)
              node))
    node))

(defun decrease-key (heap node key)
  (if (< (node-key node) key)
      (error "Cannot decrease key: new key greater than current key.")
      (setf (node-key node) key))
  (unless (eq node (slot-value heap 'root))
    (setf (slot-value heap 'root) 
          (link (slot-value heap 'root)
                (cut-parent node))))
  node)

(defun extract-node (heap node)
  (let ((root (slot-value heap 'root)))
    (cond
      ((eq root node)
       (extract-min heap))
      (t
       (cut-parent node)
       (let ((tmp (make-instance 'pairing-heap
                                 :size 1
                                 :root node)))
         ;(declare (dynamic-extent tmp))
         (prog1 (extract-min tmp)
           (meld heap tmp)))))))

(defun meld (heap-a heap-b)
  "Melds HEAP-A and HEAP-B into HEAP-A and returns it. HEAP-B will be
empty after this operation but may be used further."
  (incf (slot-value heap-a 'size) (slot-value heap-b 'size))
  (setf (slot-value heap-a 'root)
        (link (slot-value heap-a 'root)
              (slot-value heap-b 'root)))
  (clear-heap heap-b)
  heap-a)


;;; internal structure maintaining functions
;(declaim (inline attach-child link))

(defun attach-child (parent child)
  (push child (node-children parent))
  (setf (node-parent child) parent))

(defun link (node-a node-b)
  (cond
    ;((null node-a) node-b)
    ;((null node-b) node-a)
    ((< (node-key node-a) (node-key node-b))
     (attach-child node-a node-b))
    (t (attach-child node-b node-a))))

(defun combine-siblings (parent)
  (link-children (pair-children parent)))

(defun pair-children (parent)
  (let ((children (node-children parent)))
    (setf (node-children parent) nil)
    (loop for childs on children by #'cddr
          while childs
          do (if (cdr childs)
                 (attach-child parent (link (car childs)
                                            (cadr childs)))
                 (attach-child parent (car childs)))
          finally (return parent))))

(defun link-children (parent)
  (when (node-children parent)
    (loop for root = (car (node-children parent)) then (link root c)
          for c in (cdr (node-children parent))
          finally (setf (node-children parent) (list root))
                  (return root))))

(defun cut-parent (node)
  (let ((parent (node-parent node)))
    (when parent
      (setf (node-children parent)
            (delete node (node-children parent) :test #'eq :count 1)))
    (setf (node-parent node) nil))
  node)