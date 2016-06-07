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

(defpackage :pairing-heap (:use :cl)
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

(in-package :pairing-heap)

;;;; Pairing min-heap, see "L. Fredman, R. Sedgewick, D. Sleator and
;;;; R. Tarjan 'The Pairing Heap: A New Form of Self-Adjusting
;;;; Heap', Algorithmica (1986) 1: 111--129."

(defstruct (node (:constructor %make-node (key data)))
  (key 0 :type fixnum)
  (data nil)
  (lchild nil  :type (or null node))
  (sibling nil :type (or null node))
  (parent nil  :type (or null node)))

(defclass pairing-heap ()
  ((size :initform 0 :initarg :size
         :type (integer 0 *))
   (root :initform nil :initarg :root
         :type (or null node))))

(defmethod print-object ((obj pairing-heap) stream)
  (print-unreadable-object (obj stream :type t :identity t)
    (format stream "~4I~:_size: ~A~:_" (slot-value obj 'size))))

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
    (when node
      (values (node-data node)
              (node-key node)))))

(defun extract-min (heap)
  (let ((node (slot-value heap 'root)))
    (assert node)
    (setf (slot-value heap 'root)
          (combine-siblings node))
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
       (decf (slot-value heap 'size))
       (cut-parent node)
       (let ((tmp (make-instance 'pairing-heap
                                 :size 1
                                 :root node)))
         ;(declare (dynamic-extent tmp))
         (prog1 (extract-min tmp)
           (when (slot-value tmp 'root)
             (meld heap tmp))))))))

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

(defun attach-child (parent child)
  (shiftf (node-sibling child) (node-lchild parent) child)
  (setf (node-parent child) parent))

(defun link (node-a node-b)
  (cond
    ;((null node-a) node-b)
    ;((null node-b) node-a)
    ((< (node-key node-a) (node-key node-b))
     (attach-child node-a node-b))
    (t (attach-child node-b node-a))))

(defun combine-siblings (parent)
  (pair-children parent)
  (link-children parent))

(defun pair-children (parent)
  (when (node-lchild parent)
    (loop for c1 = (shiftf (node-lchild parent) nil) then next
          for c2 = (node-sibling c1)
          with next
          do (if c2
                 (progn
                   (setf (node-sibling c1) nil
                         next (shiftf (node-sibling c2) nil))
                   (attach-child parent (link c1 c2)))
                 (attach-child parent c1))
          while (and c2 next))))

(defun link-children (parent)
  (let ((root (node-lchild parent)))
    (when root
      (loop for child = (shiftf (node-sibling root) nil) 
              then (prog1 (shiftf (node-sibling child) nil)
                     (setf root (link root child)))
            while child
            finally (return root)))))

(defun cut-parent (node)
  (let ((parent (node-parent node)))
    (when parent
      (setf (node-lchild parent)
            (delete-node-from-childseq node
                                       (node-lchild parent))))
    node))

(defun delete-node-from-childseq (node first-child)
  (if (eq node first-child)
      (setf first-child (node-sibling node))
      (loop for c = first-child then next
            for next = (node-sibling c)
            until (eq node next)
            finally (setf (node-sibling c)
                          (node-sibling next))))
  (setf (node-parent node) nil
        (node-sibling node) nil)
  first-child)
